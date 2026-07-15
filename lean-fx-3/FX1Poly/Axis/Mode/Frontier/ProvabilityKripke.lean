import FX1Poly.Axis.Mode.Provability

/-! # mode-23 frontier — GL Kripke semantics: syntax, soundness, and a concrete countermodel

`FX1Poly/Axis/Mode/Provability.lean` ships the SEMANTIC soundness of GL (Gödel-Löb): `boxOver_loeb` proves the
Löb axiom `□(□φ → φ) → □φ` is valid on transitive + converse-well-founded frames.  That is the validity / soundness
side of GL.  This file builds the SYNTACTIC side and crosses the two:

  * a syntactic GL formula type `GLFormula` (`atom n` / `bot` / `imp` / `box`) and a Hilbert-style derivability
    inductive `GLProves` (the classical implicational+falsum base, K, axiom 4, Löb, necessitation, modus ponens);
  * Kripke `forces` over an accessibility relation + a Boolean atom valuation, with the box clause defined as
    `boxOver` so the GL modal lemmas of `Provability.lean` are reused VERBATIM;
  * ★ `glProves_sound` — SOUNDNESS: every `GLProves` theorem is forced at every world of every transitive +
    converse-well-founded frame whose forcing is two-valued (the classical-logic decidability side condition, which
    every concrete finite model discharges).  K reuses `boxOver_distrib`, 4 reuses `boxOver_four`, Löb reuses
    `boxOver_loeb`, necessitation reuses `boxOver_necessitation`;
  * ★ the concrete one-point dead-end frame `deadEndFrame`, the proof that its forcing is two-valued, and
    ★★ `not_glProves_box_atom_imp_atom` — the **contrapositive-of-completeness witness**: the T axiom `□p → p` is
    NOT a GL theorem, because it is refuted at the dead-end world (where `□p` holds vacuously but `p` is false).
    This is the consistency / non-triviality of GL: a concrete non-theorem, exhibited by a finite countermodel.

## Scope (honest)

This ships GL SOUNDNESS over finite transitive irreflexive frames + a concrete finite countermodel for a specific
non-theorem (the contrapositive-of-completeness witness).  It does NOT ship the canonical-model / Fischer-Ladner
filtration + truth-lemma construction that gives FULL completeness (every frame-valid formula is GL-derivable);
that remains the research-grade construction.  See the marker discussion at the foot of the file.

Zero external dependencies; raw Lean 4 + Init only.  Every declaration is free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`.
-/

namespace FX1Poly.Axis

/-! ## Syntax -/

/-- A GL (provability-logic) formula over `{imp, bot, box}` with `Nat`-indexed atoms.  `not`, `and`, `or`, `top`
are the usual classical abbreviations over this minimal base (see `glNot`). -/
inductive GLFormula : Type where
  | atom (index : Nat) : GLFormula
  | bot : GLFormula
  | imp (antecedent consequent : GLFormula) : GLFormula
  | box (inner : GLFormula) : GLFormula
  deriving Repr

/-- Negation as the classical abbreviation `¬φ := φ → ⊥`. -/
def glNot (formula : GLFormula) : GLFormula := GLFormula.imp formula GLFormula.bot

/-! ## Derivability — the Hilbert calculus for GL

A complete classical implicational+falsum base (PL1/PL2/PL3 over `{imp, bot}` with modus ponens), plus the modal
axioms K and 4, the Löb axiom (which makes this GL rather than K4), and the necessitation rule. -/

/-- The GL derivability relation `⊢ φ`.  PL3 is classical double-negation elimination, so `GLProves` is the FULL
classical GL, not its intuitionistic fragment. -/
inductive GLProves : GLFormula → Prop where
  /-- PL1: `φ → (ψ → φ)`. -/
  | propWeaken (first second : GLFormula) :
      GLProves (GLFormula.imp first (GLFormula.imp second first))
  /-- PL2: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | propDistribute (first second third : GLFormula) :
      GLProves (GLFormula.imp
        (GLFormula.imp first (GLFormula.imp second third))
        (GLFormula.imp (GLFormula.imp first second) (GLFormula.imp first third)))
  /-- PL3 (classical): `((φ → ⊥) → ⊥) → φ` — double-negation elimination. -/
  | propDoubleNegation (formula : GLFormula) :
      GLProves (GLFormula.imp (glNot (glNot formula)) formula)
  /-- The K axiom `□(φ → ψ) → (□φ → □ψ)`. -/
  | axiomK (premise conclusion : GLFormula) :
      GLProves (GLFormula.imp
        (GLFormula.box (GLFormula.imp premise conclusion))
        (GLFormula.imp (GLFormula.box premise) (GLFormula.box conclusion)))
  /-- The 4 axiom `□φ → □□φ`. -/
  | axiomFour (inner : GLFormula) :
      GLProves (GLFormula.imp (GLFormula.box inner) (GLFormula.box (GLFormula.box inner)))
  /-- The Löb axiom `□(□φ → φ) → □φ` (the defining GL axiom). -/
  | axiomLoeb (inner : GLFormula) :
      GLProves (GLFormula.imp
        (GLFormula.box (GLFormula.imp (GLFormula.box inner) inner))
        (GLFormula.box inner))
  /-- Necessitation: from `⊢ φ` conclude `⊢ □φ`. -/
  | necessitation (inner : GLFormula) :
      GLProves inner → GLProves (GLFormula.box inner)
  /-- Modus ponens: from `⊢ φ → ψ` and `⊢ φ` conclude `⊢ ψ`. -/
  | modusPonens (antecedent consequent : GLFormula) :
      GLProves (GLFormula.imp antecedent consequent) → GLProves antecedent → GLProves consequent

/-! ## Kripke semantics

A model is an accessibility relation plus a Boolean valuation of the atoms.  Forcing is `Prop`-valued so the box
clause can be defined directly as `boxOver`, letting the GL modal lemmas of `Provability.lean` be reused without a
`Bool`/`Prop` bridge. -/

/-- Forcing of a GL formula at a world, over accessibility `accessible` and atom valuation `valuation`.  The box
clause is exactly `boxOver`, so `forces … (box φ)` reduces definitionally to "φ is forced at every successor". -/
def forces {World : Type} (accessible : World → World → Prop) (valuation : Nat → World → Bool) :
    GLFormula → World → Prop
  | GLFormula.atom index, world => valuation index world = true
  | GLFormula.bot, _ => False
  | GLFormula.imp antecedent consequent, world =>
      forces accessible valuation antecedent world → forces accessible valuation consequent world
  | GLFormula.box inner, world =>
      boxOver accessible (forces accessible valuation inner) world

/-- The box clause of `forces`, stated against `boxOver` so the modal lemmas of `Provability.lean` apply
pointwise.  Holds by definitional unfolding (no axiom). -/
theorem forces_box_eq_boxOver {World : Type} (accessible : World → World → Prop)
    (valuation : Nat → World → Bool) (inner : GLFormula) (world : World) :
    forces accessible valuation (GLFormula.box inner) world =
      boxOver accessible (forces accessible valuation inner) world :=
  rfl

/-- A model is *two-valued* (classical) when forcing of every formula at every world either holds or fails.  This
is exactly the side condition that makes classical double-negation elimination semantically sound; every concrete
finite model satisfies it (proved for the dead-end frame below). -/
def IsTwoValuedModel {World : Type} (accessible : World → World → Prop)
    (valuation : Nat → World → Bool) : Prop :=
  ∀ formula world, forces accessible valuation formula world ∨ ¬ forces accessible valuation formula world

/-! ## Soundness

Every GL theorem is forced at every world of every transitive + converse-well-founded two-valued frame.  The modal
cases delegate to `Provability.lean`; the propositional cases are constructive once the model is two-valued. -/

/-- ★ **Soundness of GL** w.r.t. transitive + converse-well-founded frames with two-valued forcing.  K reuses
`boxOver_distrib`, axiom 4 reuses `boxOver_four`, the Löb axiom reuses `boxOver_loeb`, necessitation reuses
`boxOver_necessitation`; the three propositional axioms are discharged from two-valuedness. -/
theorem glProves_sound {World : Type} (accessible : World → World → Prop)
    (valuation : Nat → World → Bool)
    (isTransitive : IsTransitiveFrame accessible)
    (isConverseWellFounded : ConverseWellFounded accessible)
    (isTwoValued : IsTwoValuedModel accessible valuation)
    {formula : GLFormula} (derivation : GLProves formula) :
    ∀ world, forces accessible valuation formula world := by
  induction derivation with
  | propWeaken first second =>
    intro world forcedFirst _
    exact forcedFirst
  | propDistribute first second third =>
    intro world forcedNested forcedAntToCons forcedAnt
    exact forcedNested forcedAnt (forcedAntToCons forcedAnt)
  | propDoubleNegation inner =>
    intro world forcedDoubleNegation
    cases isTwoValued inner world with
    | inl forcedInner => exact forcedInner
    | inr refutedInner => exact (forcedDoubleNegation refutedInner).elim
  | axiomK premise conclusion =>
    intro world boxedImplication boxedPremise
    exact boxOver_distrib accessible
      (forces accessible valuation premise) (forces accessible valuation conclusion)
      world boxedImplication boxedPremise
  | axiomFour inner =>
    intro world boxedInner
    exact boxOver_four accessible isTransitive (forces accessible valuation inner) world boxedInner
  | axiomLoeb inner =>
    intro world premiseHolds
    exact boxOver_loeb accessible isTransitive isConverseWellFounded
      (forces accessible valuation inner) world premiseHolds
  | necessitation inner _ innerForcedEverywhere =>
    intro world
    exact boxOver_necessitation accessible (forces accessible valuation inner) world
      innerForcedEverywhere
  | modusPonens antecedent consequent _ _ impForcedEverywhere antForcedEverywhere =>
    intro world
    exact impForcedEverywhere world (antForcedEverywhere world)

/-! ## A concrete countermodel — the contrapositive-of-completeness witness

The one-point *dead-end* frame: a single world with no outgoing edges.  It is transitive and converse-well-founded
trivially (the empty relation), and `□φ` holds vacuously at the dead end for every `φ`.  Choosing a valuation that
falsifies the atom refutes the T axiom `□p → p`, exhibiting it as a concrete GL non-theorem. -/

/-- The single world of the dead-end frame. -/
inductive DeadEndWorld : Type where
  | only : DeadEndWorld
  deriving Repr

/-- The empty accessibility relation on the dead-end world: no world is accessible from any world. -/
def deadEndAccessible : DeadEndWorld → DeadEndWorld → Prop :=
  fun _ _ => False

/-- The valuation falsifying every atom at the dead-end world. -/
def deadEndValuation : Nat → DeadEndWorld → Bool :=
  fun _ _ => false

/-- The dead-end frame is transitive (vacuously — there are no edges to compose). -/
theorem deadEndFrame_isTransitive : IsTransitiveFrame deadEndAccessible :=
  fun _ _ _ noFirstEdge _ => noFirstEdge.elim

/-- The dead-end frame is converse-well-founded: the only world has no predecessor under the converse relation, so
it is `Acc` immediately. -/
theorem deadEndFrame_isConverseWellFounded : ConverseWellFounded deadEndAccessible :=
  fun world => Acc.intro world (fun _ noEdge => noEdge.elim)

/-- The dead-end model is two-valued: forcing is decided for every formula by structural recursion (atoms by the
`Bool` valuation, `⊥` always failing, implication classically combining the decided subformulas, the box always
holding vacuously). -/
theorem deadEndFrame_isTwoValued : IsTwoValuedModel deadEndAccessible deadEndValuation := by
  intro formula
  induction formula with
  | atom index =>
    intro world
    -- `forces … (atom index) world` is defeq `deadEndValuation index world = true`, i.e. `false = true`.
    exact Or.inr (fun forcedAtom => Bool.noConfusion forcedAtom)
  | bot =>
    intro world
    exact Or.inr (fun isFalse => isFalse)
  | imp antecedent consequent decideAntecedent decideConsequent =>
    intro world
    cases decideConsequent world with
    | inl forcedConsequent => exact Or.inl (fun _ => forcedConsequent)
    | inr refutedConsequent =>
      cases decideAntecedent world with
      | inl forcedAntecedent =>
        exact Or.inr (fun forcedImplication => refutedConsequent (forcedImplication forcedAntecedent))
      | inr refutedAntecedent =>
        exact Or.inl (fun forcedAntecedent => (refutedAntecedent forcedAntecedent).elim)
  | box inner _ =>
    intro world
    -- `□φ` at the dead end is `∀ successor, False → …`, vacuously true.
    exact Or.inl (fun _ noEdge => noEdge.elim)

/-- At the dead-end world `□(atom 0)` holds (vacuously — no successors witness any atom). -/
theorem deadEndFrame_forces_box_atom :
    forces deadEndAccessible deadEndValuation (GLFormula.box (GLFormula.atom 0)) DeadEndWorld.only :=
  fun _ noEdge => noEdge.elim

/-- At the dead-end world `atom 0` is refuted (the valuation falsifies it). -/
theorem deadEndFrame_refutes_atom :
    ¬ forces deadEndAccessible deadEndValuation (GLFormula.atom 0) DeadEndWorld.only :=
  fun forcedAtom => Bool.noConfusion forcedAtom

/-- The dead-end world refutes the T axiom `□(atom 0) → atom 0`: the antecedent `□p` holds vacuously while the
consequent `p` fails. -/
theorem deadEndFrame_refutes_box_atom_imp_atom :
    ¬ forces deadEndAccessible deadEndValuation
        (GLFormula.imp (GLFormula.box (GLFormula.atom 0)) (GLFormula.atom 0)) DeadEndWorld.only :=
  fun forcedImplication =>
    deadEndFrame_refutes_atom (forcedImplication deadEndFrame_forces_box_atom)

/-- ★★ **Contrapositive-of-completeness witness.**  The T axiom `□p → p` is NOT a GL theorem.  By soundness any GL
theorem is forced at every world of the dead-end frame (transitive + converse-well-founded + two-valued), but the
dead-end world refutes `□(atom 0) → atom 0`.  This is the consistency / non-triviality of GL: a concrete formula
that GL does not prove, certified by a finite countermodel. -/
theorem not_glProves_box_atom_imp_atom :
    ¬ GLProves (GLFormula.imp (GLFormula.box (GLFormula.atom 0)) (GLFormula.atom 0)) :=
  fun derivation =>
    deadEndFrame_refutes_box_atom_imp_atom
      (glProves_sound deadEndAccessible deadEndValuation
        deadEndFrame_isTransitive deadEndFrame_isConverseWellFounded deadEndFrame_isTwoValued
        derivation DeadEndWorld.only)

/-- Corollary: GL is consistent — it does not prove `⊥` (`bot` is refuted at the dead-end world, which forces every
GL theorem). -/
theorem not_glProves_bot : ¬ GLProves GLFormula.bot :=
  fun derivation =>
    glProves_sound deadEndAccessible deadEndValuation
      deadEndFrame_isTransitive deadEndFrame_isConverseWellFounded deadEndFrame_isTwoValued
      derivation DeadEndWorld.only

/-! ## Marker note

The shipped content above is GL SOUNDNESS over finite transitive irreflexive frames (`glProves_sound`, delegating
the modal cases to `Provability.lean`) plus a concrete finite COUNTERMODEL refuting a non-theorem
(`not_glProves_box_atom_imp_atom`).  Together these are the soundness direction and the contrapositive-of-
completeness (consistency) witness.

FULL Kripke completeness — every formula valid on all finite transitive irreflexive trees is GL-derivable — needs
the canonical model over a Fischer-Ladner-closed adequate set plus the truth lemma (and, for GL specifically, the
irreflexivisation / transitive-tree unravelling).  That construction is not shipped here, so the honesty marker
`fxMode_hasKripkeCompleteness` stays `false`; the proposed docstring (below, applied by the orchestrator to
`Provability.lean`) narrows the wording to record exactly what now ships.
-/

end FX1Poly.Axis
