/-! # mode-27 — Fitch-style vs dual-context vs MTT: the presentation equivalence

The three standard PRESENTATIONS of (necessity-style) modal type theory differ only in how the CONTEXT records
modal structure — and they are inter-translatable.  This rung mechanizes the context-level presentation equivalence
for the single-mode necessity fragment (Pfenning-Davies dual-context ≃ Clouston Fitch-style ≃ Gratzer-et-al MTT):

  * **Fitch-style** (Clouston, "Fitch-Style Modal Lambda Calculi"): the context is a list of ZONES separated by
    LOCKS; `box` opens a fresh zone (adds a lock), `unbox` consumes one.  Modal depth = number of locks.
  * **dual-context** (Pfenning-Davies / Kavvos): TWO zones `(Δ; Γ)` — Δ the modal/valid zone (necessitated
    hypotheses), Γ the local/true zone.  This is exactly the SINGLE-LOCK Fitch context.
  * **MTT** (Gratzer-Kavvos-Nuyts-Birkedal): a flat list of ENTRIES, each a hypothesis or a lock `{🔒}`.  Fitch
    zones flatten to lock-separated hypothesis runs.

## What this file ships (each piece zero-axiom)

  * the three context representations: `FitchContext` (= list of zones), `DualContext` (the two-zone structure),
    `MttContext` (= list of `MttEntry` hyp/lock) + `lockDepth` / `lockCount` (the modal box-depth in each).
  * ★ the **Fitch ↔ dual-context bijection** — `dualToFitch` / `fitchToDual` + BOTH round trips
    (`fitchToDual_dualToFitch`, `dualToFitch_fitchToDual` on the two-zone fragment), each by `rfl` (structure eta).
    This is the Pfenning-Davies = single-lock-Fitch presentation equivalence, machine-checked.
  * the **Fitch → MTT** flattening `fitchToMtt` (zones → lock-separated runs) + `mttToFitch` (split at locks), with
    ★ `fitchToMtt_lockCount` — the modal box-DEPTH is PRESERVED across the translation (locks ↦ locks).
  * the tri-presentation depth agreement: `dualToFitch_lockDepth = 1` and `dual_fitchToMtt_lockCount = 1` — a
    dual-context's single box is one Fitch lock is one MTT lock.

## What is DEFERRED (markers)

  * the full MTT context round trip `mttToFitch ∘ fitchToMtt = id` (the splitting/joining bijection — needs the
    no-empty-zone invariant) (`hasMttContextRoundTrip`);
  * MTT's general MULTI-mode structure (mode-annotated locks `{🔒_μ}` over a mode theory — here a single necessity
    mode) (`hasMultiModePresentation`);
  * the TERM-level translation (box / unbox / let-box across the three calculi) + the type-preservation /
    cut-admissibility transport (here only CONTEXTS) (`hasTermLevelTranslation`);
  * the DEFINITIONAL-vs-propositional strength of the equivalence (here strict, `rfl`; the full biequivalence of
    the syntactic categories) (`hasBiequivalenceStrength`);
  * the kernel lock `◐_μ` / `MttEntry.lock` fibred into the mode doctrine (cross-axis, `fib`)
    (`hasKernelLockFibration`).

Zero external dependencies; raw Lean 4 + Init only (no mode-core import needed — this is the structural
presentation layer).
-/

namespace FX1Poly.Tier0

/-! ## The three context representations -/

/-- An **MTT context entry**: a hypothesis or a lock `{🔒}` (the modal separator). -/
inductive MttEntry (Hypothesis : Type) where
  /-- An ordinary hypothesis. -/
  | hyp (hypothesis : Hypothesis)
  /-- A modal lock (the `box`/`unbox` separator). -/
  | lock

/-- An **MTT context** — a flat list of entries (hypotheses interleaved with locks). -/
abbrev MttContext (Hypothesis : Type) : Type := List (MttEntry Hypothesis)

/-- The **modal depth** of an MTT context: the number of locks. -/
def MttContext.lockCount {Hypothesis : Type} : MttContext Hypothesis → Nat
  | [] => 0
  | MttEntry.hyp _ :: rest => MttContext.lockCount rest
  | MttEntry.lock :: rest => MttContext.lockCount rest + 1

/-- A **Fitch-style context** — a list of zones; the LOCKS are the separators between consecutive zones.  The head
zone is the innermost (current/local) zone. -/
abbrev FitchContext (Hypothesis : Type) : Type := List (List Hypothesis)

/-- The **modal depth** of a Fitch context: the number of locks = zone boundaries (zones minus one). -/
def FitchContext.lockDepth {Hypothesis : Type} : FitchContext Hypothesis → Nat
  | [] => 0
  | [_] => 0
  | _ :: (nextZone :: deeperZones) => FitchContext.lockDepth (nextZone :: deeperZones) + 1

/-- A **dual-context** (Pfenning-Davies): the modal/valid zone `Δ` and the local/true zone `Γ`. -/
structure DualContext (Hypothesis : Type) where
  /-- The modal (valid / necessitated) zone Δ. -/
  modalZone : List Hypothesis
  /-- The local (true) zone Γ. -/
  localZone : List Hypothesis

/-! ## The Fitch ↔ dual-context bijection (Pfenning-Davies = single-lock Fitch) -/

/-- A dual-context becomes the two-zone (single-lock) Fitch context `[Γ, Δ]` (head = local, then a lock, then modal). -/
def dualToFitch {Hypothesis : Type} (dual : DualContext Hypothesis) : FitchContext Hypothesis :=
  [dual.localZone, dual.modalZone]

/-- A Fitch context collapses to a dual-context: head = local zone, second = modal zone (deeper zones merged away —
the bijection holds exactly on the two-zone fragment). -/
def fitchToDual {Hypothesis : Type} : FitchContext Hypothesis → DualContext Hypothesis
  | localZone :: modalZone :: _ => { localZone := localZone, modalZone := modalZone }
  | [localZone] => { localZone := localZone, modalZone := [] }
  | [] => { localZone := [], modalZone := [] }

/-- ★ Round trip one: `fitchToDual ∘ dualToFitch = id` (every dual-context survives the translation, by structure eta). -/
theorem fitchToDual_dualToFitch {Hypothesis : Type} (dual : DualContext Hypothesis) :
    fitchToDual (dualToFitch dual) = dual := rfl

/-- ★ Round trip two: `dualToFitch ∘ fitchToDual = id` on the two-zone fragment (the single-lock Fitch contexts —
exactly the dual-context calculus). -/
theorem dualToFitch_fitchToDual {Hypothesis : Type} (localZone modalZone : List Hypothesis) :
    dualToFitch (fitchToDual [localZone, modalZone]) = [localZone, modalZone] := rfl

/-- The dual-context's image has modal depth exactly `1` — a single box. -/
theorem dualToFitch_lockDepth {Hypothesis : Type} (dual : DualContext Hypothesis) :
    (dualToFitch dual).lockDepth = 1 := rfl

/-! ## The Fitch → MTT flattening (zones ↦ lock-separated runs) -/

/-- Flatten a Fitch context to an MTT context: each zone's hypotheses become `hyp` entries, with a `lock` between
consecutive zones. -/
def fitchToMtt {Hypothesis : Type} : FitchContext Hypothesis → MttContext Hypothesis
  | [] => []
  | zone :: [] => zone.map MttEntry.hyp
  | zone :: (nextZone :: deeperZones) =>
      zone.map MttEntry.hyp ++ MttEntry.lock :: fitchToMtt (nextZone :: deeperZones)

/-- Split an MTT context back into Fitch zones at the locks (head zone = innermost). -/
def mttToFitch {Hypothesis : Type} : MttContext Hypothesis → FitchContext Hypothesis
  | [] => [[]]
  | MttEntry.hyp hypothesis :: rest =>
      match mttToFitch rest with
      | currentZone :: outerZones => (hypothesis :: currentZone) :: outerZones
      | [] => [[hypothesis]]
  | MttEntry.lock :: rest => [] :: mttToFitch rest

/-- A run of mapped hypotheses contributes no locks. -/
theorem lockCount_mapHyp {Hypothesis : Type} (zone : List Hypothesis) :
    MttContext.lockCount (zone.map MttEntry.hyp) = 0 := by
  induction zone with
  | nil => rfl
  | cons _ rest ih => exact ih

/-- `lockCount` distributes over append. -/
theorem lockCount_append {Hypothesis : Type} (entriesLeft entriesRight : MttContext Hypothesis) :
    (entriesLeft ++ entriesRight).lockCount = entriesLeft.lockCount + entriesRight.lockCount := by
  induction entriesLeft with
  | nil => rw [List.nil_append, MttContext.lockCount, Nat.zero_add]
  | cons entry rest ih =>
    cases entry with
    | hyp _ => rw [List.cons_append, MttContext.lockCount, MttContext.lockCount, ih]
    | lock =>
      rw [List.cons_append, MttContext.lockCount, MttContext.lockCount, ih, Nat.succ_add]

/-- ★ The modal box-DEPTH is preserved by the Fitch → MTT flattening: locks map to locks. -/
theorem fitchToMtt_lockCount {Hypothesis : Type} (context : FitchContext Hypothesis) :
    (fitchToMtt context).lockCount = context.lockDepth := by
  induction context with
  | nil => rfl
  | cons zone rest ih =>
    cases rest with
    | nil => exact lockCount_mapHyp zone
    | cons nextZone deeperZones =>
      show MttContext.lockCount ((zone.map MttEntry.hyp) ++ MttEntry.lock :: fitchToMtt (nextZone :: deeperZones))
        = FitchContext.lockDepth (nextZone :: deeperZones) + 1
      rw [lockCount_append, lockCount_mapHyp, MttContext.lockCount, ih, Nat.zero_add]

/-- ★ The tri-presentation depth agreement: a dual-context flattens (via its Fitch image) to an MTT context with
exactly one lock — its single box is one Fitch lock is one MTT lock. -/
theorem dual_fitchToMtt_lockCount {Hypothesis : Type} (dual : DualContext Hypothesis) :
    (fitchToMtt (dualToFitch dual)).lockCount = 1 := by
  rw [fitchToMtt_lockCount, dualToFitch_lockDepth]

/-! ## The MTT context round trip (the splitting/joining bijection) -/

/-- `l ++ [] = l`, proved propext-free (the stdlib `List.append_nil` depends on `propext`; `cons_append` is clean). -/
theorem appendEmptyRight {Hypothesis : Type} (entries : List Hypothesis) : entries ++ [] = entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih => rw [List.cons_append, ih]

/-- Prepend a zone's hypotheses onto the head (innermost) zone of a Fitch context. -/
def prependZone {Hypothesis : Type} (hypotheses : List Hypothesis) :
    FitchContext Hypothesis → FitchContext Hypothesis
  | currentZone :: outerZones => (hypotheses ++ currentZone) :: outerZones
  | [] => [hypotheses]

/-- Prepending always yields a nonempty context (both branches produce a cons). -/
theorem prependZone_ne_nil {Hypothesis : Type} (hypotheses : List Hypothesis)
    (context : FitchContext Hypothesis) : prependZone hypotheses context ≠ [] := by
  cases context with
  | nil => show [hypotheses] ≠ []; exact List.cons_ne_nil _ _
  | cons currentZone outerZones =>
    show (hypotheses ++ currentZone) :: outerZones ≠ []; exact List.cons_ne_nil _ _

/-- `mttToFitch` on a hypothesis entry is prepending that hypothesis to the head zone (definitional). -/
theorem mttToFitch_hyp {Hypothesis : Type} (hypothesis : Hypothesis) (rest : MttContext Hypothesis) :
    mttToFitch (MttEntry.hyp hypothesis :: rest) = prependZone [hypothesis] (mttToFitch rest) := rfl

/-- `mttToFitch` always returns at least one zone (the innermost zone is always present). -/
theorem mttToFitch_ne_nil {Hypothesis : Type} (context : MttContext Hypothesis) :
    mttToFitch context ≠ [] := by
  cases context with
  | nil => exact List.cons_ne_nil _ _
  | cons entry rest =>
    cases entry with
    | hyp hypothesis => rw [mttToFitch_hyp]; exact prependZone_ne_nil [hypothesis] (mttToFitch rest)
    | lock => show [] :: mttToFitch rest ≠ []; exact List.cons_ne_nil _ _

/-- Prepending composes: a singleton then a tail equals the cons. -/
theorem prependZone_compose {Hypothesis : Type} (firstHyp : Hypothesis) (restHyps : List Hypothesis)
    (context : FitchContext Hypothesis) :
    prependZone [firstHyp] (prependZone restHyps context) = prependZone (firstHyp :: restHyps) context := by
  cases context with
  | nil => rfl
  | cons currentZone outerZones => rfl

/-- Flattening a zone's hypotheses then splitting reattaches them to the head zone. -/
theorem mttToFitch_mapHyp_append {Hypothesis : Type} (zone : List Hypothesis) (rest : MttContext Hypothesis) :
    mttToFitch (zone.map MttEntry.hyp ++ rest) = prependZone zone (mttToFitch rest) := by
  induction zone with
  | nil =>
    show mttToFitch rest = prependZone [] (mttToFitch rest)
    cases hReached : mttToFitch rest with
    | nil => exact absurd hReached (mttToFitch_ne_nil rest)
    | cons currentZone outerZones => rfl
  | cons firstHyp restHyps ih =>
    show mttToFitch (MttEntry.hyp firstHyp :: (restHyps.map MttEntry.hyp ++ rest))
       = prependZone (firstHyp :: restHyps) (mttToFitch rest)
    rw [mttToFitch_hyp, ih, prependZone_compose]

/-- ★ The full **MTT context round trip** `mttToFitch ∘ fitchToMtt = id` on genuine (nonempty-zone) Fitch contexts —
the splitting and joining are mutually inverse, so the Fitch and MTT presentations are isomorphic (not merely
lock-depth-agreeing). -/
theorem mttToFitch_fitchToMtt {Hypothesis : Type} (firstZone : List Hypothesis)
    (restZones : FitchContext Hypothesis) :
    mttToFitch (fitchToMtt (firstZone :: restZones)) = firstZone :: restZones := by
  induction restZones generalizing firstZone with
  | nil =>
    show mttToFitch (firstZone.map MttEntry.hyp) = [firstZone]
    rw [← appendEmptyRight (firstZone.map MttEntry.hyp), mttToFitch_mapHyp_append]
    show (firstZone ++ []) :: [] = [firstZone]
    rw [appendEmptyRight]
  | cons secondZone deeperZones ih =>
    show mttToFitch (firstZone.map MttEntry.hyp ++ MttEntry.lock :: fitchToMtt (secondZone :: deeperZones))
       = firstZone :: secondZone :: deeperZones
    rw [mttToFitch_mapHyp_append]
    show prependZone firstZone ([] :: mttToFitch (fitchToMtt (secondZone :: deeperZones)))
       = firstZone :: secondZone :: deeperZones
    rw [ih secondZone]
    show (firstZone ++ []) :: (secondZone :: deeperZones) = firstZone :: secondZone :: deeperZones
    rw [appendEmptyRight]

/-! ## The term-level translation (box / unbox / let-box across the calculi) -/

/-- **Fitch-style modal terms** (Clouston, necessity fragment): variables, λ/application, `boxIntro`
(□-introduction — opens a lock), and the COERCIVE unary `unbox` (consumes one lock).  This is Clouston's surface
syntax — the eliminator is a unary coercion, NOT a binder. -/
inductive FitchModalTerm where
  /-- A de Bruijn variable. -/
  | var (index : Nat)
  /-- λ-abstraction. -/
  | lam (body : FitchModalTerm)
  /-- Application. -/
  | app (fn : FitchModalTerm) (arg : FitchModalTerm)
  /-- □-introduction (`box`). -/
  | boxIntro (body : FitchModalTerm)
  /-- The coercive unary `unbox` (consumes one lock). -/
  | unbox (scrutinee : FitchModalTerm)

/-- **MTT / dual-context modal terms** (Gratzer-et-al / Pfenning-Davies, necessity fragment): the BINDING
elimination `modElim` (`let mod x = · in ·` / `let box`) rather than a coercion. -/
inductive MttModalTerm where
  /-- A de Bruijn variable. -/
  | var (index : Nat)
  /-- λ-abstraction. -/
  | lam (body : MttModalTerm)
  /-- Application. -/
  | app (fn : MttModalTerm) (arg : MttModalTerm)
  /-- The modal introduction `mod_μ` (`box`). -/
  | modIntro (body : MttModalTerm)
  /-- The BINDING modal elimination `let mod x = scrutinee in body`. -/
  | modElim (scrutinee : MttModalTerm) (body : MttModalTerm)

/-- Translate a Fitch-style term to an MTT/dual-context term: `box ↦ mod`, and the coercive `unbox e` becomes the
binding `let mod x = e in x` (`modElim (tr e) (var 0)`) — the standard Fitch→dual-context term translation. -/
def fitchToMttTerm : FitchModalTerm → MttModalTerm
  | .var index => .var index
  | .lam body => .lam (fitchToMttTerm body)
  | .app fn arg => .app (fitchToMttTerm fn) (fitchToMttTerm arg)
  | .boxIntro body => .modIntro (fitchToMttTerm body)
  | .unbox scrutinee => .modElim (fitchToMttTerm scrutinee) (.var 0)

/-- Translate an MTT/dual-context term back to Fitch: `mod ↦ box`, and the binding `let mod x = s in b` desugars to
`(λx. b) (unbox s)` (`app (lam (tr b)) (unbox (tr s))`) — let-box as application of the coercion. -/
def mttToFitchTerm : MttModalTerm → FitchModalTerm
  | .var index => .var index
  | .lam body => .lam (mttToFitchTerm body)
  | .app fn arg => .app (mttToFitchTerm fn) (mttToFitchTerm arg)
  | .modIntro body => .boxIntro (mttToFitchTerm body)
  | .modElim scrutinee body => .app (.lam (mttToFitchTerm body)) (.unbox (mttToFitchTerm scrutinee))

/-- The coercive `unbox e` translates to the binding `let mod x = e in x` (definitional — documents the
unbox↦let-box correspondence). -/
theorem fitchToMttTerm_unbox (scrutinee : FitchModalTerm) :
    fitchToMttTerm (.unbox scrutinee) = .modElim (fitchToMttTerm scrutinee) (.var 0) := rfl

/-- The binding `let mod x = s in b` translates to `(λx. b) (unbox s)` (definitional — documents the
let-box↦application-of-unbox desugaring). -/
theorem mttToFitchTerm_modElim (scrutinee body : MttModalTerm) :
    mttToFitchTerm (.modElim scrutinee body)
      = .app (.lam (mttToFitchTerm body)) (.unbox (mttToFitchTerm scrutinee)) := rfl

/-- The **modal box-count** of a Fitch term — the number of `box` introductions (the term-level modal degree). -/
def FitchModalTerm.boxCount : FitchModalTerm → Nat
  | .var _ => 0
  | .lam body => body.boxCount
  | .app fn arg => fn.boxCount + arg.boxCount
  | .boxIntro body => body.boxCount + 1
  | .unbox scrutinee => scrutinee.boxCount

/-- The **modal box-count** of an MTT term — the number of `mod` introductions. -/
def MttModalTerm.modCount : MttModalTerm → Nat
  | .var _ => 0
  | .lam body => body.modCount
  | .app fn arg => fn.modCount + arg.modCount
  | .modIntro body => body.modCount + 1
  | .modElim scrutinee body => scrutinee.modCount + body.modCount

/-- ★ The Fitch→MTT term translation PRESERVES the modal box-count (`box ↦ mod`, the elims contribute none). -/
theorem fitchToMttTerm_modCount (term : FitchModalTerm) :
    (fitchToMttTerm term).modCount = term.boxCount := by
  induction term with
  | var _ => rfl
  | lam body ih => exact ih
  | app fn arg ihFn ihArg =>
      show (fitchToMttTerm fn).modCount + (fitchToMttTerm arg).modCount = fn.boxCount + arg.boxCount
      rw [ihFn, ihArg]
  | boxIntro body ih =>
      show (fitchToMttTerm body).modCount + 1 = body.boxCount + 1
      rw [ih]
  | unbox scrutinee ih =>
      show (fitchToMttTerm scrutinee).modCount + 0 = scrutinee.boxCount
      exact ih

/-- ★ The MTT→Fitch term translation PRESERVES the modal box-count (`mod ↦ box`, the let-box desugaring threads the
counts of its two subterms unchanged). -/
theorem mttToFitchTerm_boxCount (term : MttModalTerm) :
    (mttToFitchTerm term).boxCount = term.modCount := by
  induction term with
  | var _ => rfl
  | lam body ih => exact ih
  | app fn arg ihFn ihArg =>
      show (mttToFitchTerm fn).boxCount + (mttToFitchTerm arg).boxCount = fn.modCount + arg.modCount
      rw [ihFn, ihArg]
  | modIntro body ih =>
      show (mttToFitchTerm body).boxCount + 1 = body.modCount + 1
      rw [ih]
  | modElim scrutinee body ihS ihB =>
      show (mttToFitchTerm body).boxCount + (mttToFitchTerm scrutinee).boxCount
        = scrutinee.modCount + body.modCount
      rw [ihB, ihS, Nat.add_comm]

/-! ## Honesty markers -/

/-- The full MTT context round trip `mttToFitch ∘ fitchToMtt = id` is SHIPPED for genuine (nonempty-zone) Fitch
contexts — see `mttToFitch_fitchToMtt`.  `= true`. -/
def fxMode_hasMttContextRoundTrip : Bool := true

/-- ★ **Honesty marker — the multi-mode presentation ships** (`Frontier/PresentationMultiMode.lean`).  MTT's general
MULTI-mode structure (mode-annotated locks `{🔒_μ}` over a parametric mode set) is mechanized:
`MttEntryMulti`/`MttContextMulti` carry a parametric mode annotation on each lock, with a total lock count
(`lockCountMulti`) and a per-mode count (`lockCountAt`), both monoid homomorphisms over context concatenation
(`lockCountMulti_append`, `lockCountAt_append`).  The generalization is FAITHFUL: `lockCountMulti_eq_erased` proves
the multi-mode total lock count equals this file's single-mode `MttContext.lockCount` after mode-erasure (any mode
set), and the `Mode := Unit` specialization (`lockCountMulti_unit_eq_lockCount`) recovers the shipped single mode
exactly.  `= true`. -/
def fxMode_hasMultiModePresentation : Bool := true

/-- ★ **Honesty marker — the syntactic term-level translation ships.**  Both directions of the box/unbox/let-box
term translation are mechanized: `fitchToMttTerm` (the coercive `unbox e ↦ let mod x = e in x`, `fitchToMttTerm_unbox`)
and `mttToFitchTerm` (the binding `let mod x = s in b ↦ (λx. b) (unbox s)`, `mttToFitchTerm_modElim`), each
PRESERVING the modal box-count (`fitchToMttTerm_modCount`, `mttToFitchTerm_boxCount`).  They are deliberately NOT
mutually inverse — Fitch's coercion is strictly weaker than the binding elimination, which is the genuine
presentation-strength gap (`hasBiequivalenceStrength`).  The remaining residue — TYPE-preservation /
cut-admissibility transport (which needs the typing judgments of all three calculi) — is deferred.  `= true` for
the syntactic translation. -/
def fxMode_hasTermLevelTranslation : Bool := true

/-- **Honesty marker (NARROWED).**  Object-level functoriality of the term translations ships in
`Frontier/PresentationMultiMode.lean`: `fitchToMttTerm`/`mttToFitchTerm` commute with every syntactic constructor
(`fitchToMttTerm_lam/_app/_boxIntro`, `mttToFitchTerm_lam/_app/_modIntro` — structural functors on the term
algebra), the modal box/mod-count is a grading functor into `(Nat, +, 0)` preserved by both translations AND by the
round trip (`fitchRoundTrip_boxCount`, `mttRoundTrip_modCount`), and a concrete witness
(`fitchRoundTrip_not_identity`) shows the round trip is NOT the identity.  STILL DEFERRED: the full 2-categorical
biequivalence of the syntactic categories — natural isomorphisms presented as function-equalities between the
translation functors — needs `funext`, which equals `Quot.sound` in Lean's kernel and is banned under the
zero-axiom gate.  `= false`. -/
def fxMode_hasBiequivalenceStrength : Bool := false

/-- **Honesty marker.**  The kernel lock `◐_μ` / `MttEntry.lock` fibred into the mode doctrine (cross-axis, `fib`)
is deferred.  `= false`. -/
def fxMode_hasKernelLockFibration : Bool := false

end FX1Poly.Tier0
