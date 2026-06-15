import FX1Poly.Tier0.Context.SimplicialModel

/-! # context-14 — the (∞,1)-CwF: comprehension ∞-category / natural model, context-side residue

`context-14` is the (∞,1)-CwF rung: the comprehension ∞-category / natural model interpreted in an
∞-topos.  Where `context-10` shipped the 1-categorical comprehension structure, `context-14` is its
∞-UPGRADE — and the genuine extra content over the 1-category is the SIMPLICIAL / SEGAL layer.

## What is context-side here, and what is deferred

An (∞,1)-category is, by the Joyal–Lurie / Rezk picture, a SEGAL simplicial set: a presheaf on the
simplex category Δ (`context-13`) in which an `n`-simplex is determined by its SPINE — its chain of `n`
edges — and conversely every composable chain of edges fills uniquely.  That "the spine map is a
bijection" IS the composition structure of an (∞,1)-category.  This file ships that context-side layer over
`context-13`'s site, zero-axiom:

  * the simplicial EDGE and VERTEX maps (`edge01`, `edge12`, `vertexTop`, `vertexBot`) used to read off a
    simplex's spine;
  * **`ComposableEdges`** — a composable pair of edges (target of the first = source of the second);
  * **`SimplicialSet.spineOf`** — the spine of a 2-simplex (its two edges + their proven composability);
  * **`Segal2`** — the level-2 Segal condition as a structure: `spineOf` has a two-sided inverse `fill`
    (every composable pair fills to a unique 2-simplex).  This is the (∞,1)-COMPOSITION on a simplicial
    set — the genuine "(∞,1)" content;
  * **`terminalSimplicialSet` / `terminalSegal2`** — the point as an (∞,1)-category: a genuine Segal
    witness (all laws by `rfl`, via `PUnit`'s definitional eta + proof irrelevance);
  * **`fxInftyOneCwF`** — the datum: the Segal space + its composition.

DEFERRED (honestly NOT here, recorded by the `= false` markers):
  * the NERVE of `fxBaseSubstCategory` as the RICH Segal witness (composable substitution chains) —
    the genuine non-terminal model, deferred (needs the chain-composition construction);
  * REZK COMPLETENESS (the Segal space is complete — its "identities = equivalences") —
    `hasRezkCompleteness = false`;
  * the ∞-TOPOS DESCENT (the natural model valued in an ∞-topos) — `hasInftyToposDescent = false`;
  * the NATURAL-MODEL TYPE FAMILIES (`tp : Tm → Ty` representable — the CwF's types/terms presheaves) —
    `hasNaturalModelTypeFamilies = false` (`×type+term`, the full model);
  * the UNIVALENT UNIVERSE — `hasUnivalentUniverse = false` (`×type`).

Reference: Lurie, "Higher Topos Theory"; Rezk, "A model for the homotopy theory of homotopy theory"
(complete Segal spaces); Joyal–Tierney.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

/-! ## The edge and vertex maps used to read off spines -/

/-- The edge `[1] ⟶ [2]` spanning vertices `0,1` (`0 ↦ 0`, `1 ↦ 1`). -/
def SimplexMap.edge01 : SimplexMap 1 2 where
  onElement := fun position => ⟨position.val, Nat.lt_succ_of_lt position.isLt⟩
  monotonicity := fun _ _ hle => hle

/-- The edge `[1] ⟶ [2]` spanning vertices `1,2` (`0 ↦ 1`, `1 ↦ 2`). -/
def SimplexMap.edge12 : SimplexMap 1 2 where
  onElement := fun position => ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩
  monotonicity := fun _ _ hle => Nat.succ_le_succ hle

/-- The vertex `[0] ⟶ [1]` picking the bottom endpoint (`0 ↦ 0`) — the SOURCE of an edge. -/
def SimplexMap.vertexBot : SimplexMap 0 1 where
  onElement := fun _ => ⟨0, Nat.succ_pos 1⟩
  monotonicity := fun _ _ _ => Nat.le_refl 0

/-- The vertex `[0] ⟶ [1]` picking the top endpoint (`0 ↦ 1`) — the TARGET of an edge. -/
def SimplexMap.vertexTop : SimplexMap 0 1 where
  onElement := fun _ => ⟨1, Nat.lt_succ_self 1⟩
  monotonicity := fun _ _ _ => Nat.le_refl 1

/-! ## Composable edges and the spine of a 2-simplex -/

/-- A COMPOSABLE PAIR of edges in a simplicial set: two `1`-simplices whose middle vertices agree (the
TARGET of the first equals the SOURCE of the second). -/
structure ComposableEdges (simplicialSet : SimplicialSet) where
  /-- The first edge. -/
  firstEdge : simplicialSet.simplices 1
  /-- The second edge. -/
  secondEdge : simplicialSet.simplices 1
  /-- They compose: the first edge's target is the second edge's source. -/
  compatible : simplicialSet.restrict SimplexMap.vertexTop firstEdge
    = simplicialSet.restrict SimplexMap.vertexBot secondEdge

/-- The SPINE of a `2`-simplex: its two edges `(0→1, 1→2)`, together with the proof they are composable
(both restrict to the SAME middle vertex `1`).  The compatibility holds because the two relevant
composites `[0] ⟶ [2]` — pick-top-of-`edge01` and pick-bottom-of-`edge12` — are the SAME map (`0 ↦ 1`). -/
def SimplicialSet.spineOf (simplicialSet : SimplicialSet) (simplex : simplicialSet.simplices 2) :
    ComposableEdges simplicialSet where
  firstEdge := simplicialSet.restrict SimplexMap.edge01 simplex
  secondEdge := simplicialSet.restrict SimplexMap.edge12 simplex
  compatible :=
    (simplicialSet.restrictCompose SimplexMap.vertexTop SimplexMap.edge01 simplex).symm.trans
      (simplicialSet.restrictCompose SimplexMap.vertexBot SimplexMap.edge12 simplex)

/-! ## The level-2 Segal condition (the (∞,1)-composition) -/

/-- The **level-2 Segal condition** on a simplicial set: the spine map (a `2`-simplex ↦ its composable
pair of edges) has a two-sided inverse `fill`.  Equivalently, every composable pair of edges fills to a
UNIQUE `2`-simplex — which is exactly the (associative-up-to-the-3-simplex) COMPOSITION of an
(∞,1)-category presented as a Segal space.  `fillSpine` is `spine ∘ fill = id`, `fillUnique` is
`fill ∘ spine = id`. -/
structure Segal2 (simplicialSet : SimplicialSet) where
  /-- Fill a composable pair of edges to a `2`-simplex (the composite witness). -/
  fill : ComposableEdges simplicialSet → simplicialSet.simplices 2
  /-- The fill realizes the given spine: `spine (fill pair) = pair`. -/
  fillSpine : ∀ (pair : ComposableEdges simplicialSet), simplicialSet.spineOf (fill pair) = pair
  /-- The fill is the unique such simplex: `fill (spine simplex) = simplex`. -/
  fillUnique : ∀ (simplex : simplicialSet.simplices 2),
    fill (simplicialSet.spineOf simplex) = simplex

/-! ## The point as an (∞,1)-category (the terminal Segal space) -/

/-- The terminal simplicial set — one simplex in every dimension (the point). -/
def terminalSimplicialSet : SimplicialSet where
  simplices := fun _ => PUnit
  restrict := fun _ _ => PUnit.unit
  restrictIdentity := fun _ _ => rfl
  restrictCompose := fun _ _ _ => rfl

/-- ★ The point IS a Segal space (a genuine (∞,1)-category): the spine map on the terminal simplicial set
is a bijection, with every law holding by `rfl` (via `PUnit`'s definitional eta and proof irrelevance). -/
def terminalSegal2 : Segal2 terminalSimplicialSet where
  fill := fun _ => PUnit.unit
  fillSpine := fun _ => rfl
  fillUnique := fun _ => rfl

/-! ## The (∞,1)-CwF datum + honesty markers -/

/-- The context-side datum of an (∞,1)-CwF: a Segal space (the (∞,1)-category of contexts) with its
composition. -/
structure InftyOneCwFData where
  /-- The space of contexts as a simplicial set. -/
  space : SimplicialSet
  /-- The level-2 Segal composition (the (∞,1)-structure). -/
  segalComposition : Segal2 space

/-- ★ The FX (∞,1)-CwF datum — shipped at the point (the terminal Segal space).  The rich witness (the
nerve of `fxBaseSubstCategory`) is deferred; see the markers. -/
def fxInftyOneCwF : InftyOneCwFData where
  space := terminalSimplicialSet
  segalComposition := terminalSegal2

/-- **Honesty marker.**  The RICH Segal witness — the NERVE of `fxBaseSubstCategory` (composable
substitution chains), the genuine non-terminal (∞,1)-category of contexts — is not shipped here (it needs
the chain-composition construction).  `= false`. -/
def fxInftyOneCwF_hasNerveWitness : Bool := false

/-- **Honesty marker.**  REZK COMPLETENESS — the Segal space is complete (its path space of identities is
the space of equivalences) — is not shipped here.  `= false`. -/
def fxInftyOneCwF_hasRezkCompleteness : Bool := false

/-- **Honesty marker.**  ∞-TOPOS DESCENT — the natural model valued in an ∞-topos (descent / the
object classifier) — is the deep semantic content, deferred to `fib`.  `= false`. -/
def fxInftyOneCwF_hasInftyToposDescent : Bool := false

/-- **Honesty marker.**  The NATURAL-MODEL TYPE FAMILIES — Awodey's `tp : Tm → Ty` representable
natural transformation (the CwF's types and terms presheaves) — are `×type+term`, the full model,
deferred to `fib`.  `= false`. -/
def fxInftyOneCwF_hasNaturalModelTypeFamilies : Bool := false

/-- **Honesty marker.**  The UNIVALENT UNIVERSE is `×type`, deferred to the type axis / `fib`.
`= false`. -/
def fxInftyOneCwF_hasUnivalentUniverse : Bool := false

/-! ## Smoke -/

/-- Smoke: in the terminal (∞,1)-category, filling a composable pair then taking its spine returns the
pair (the Segal round-trip). -/
theorem terminalSegal2_fillSpine_smoke (pair : ComposableEdges terminalSimplicialSet) :
    terminalSimplicialSet.spineOf (terminalSegal2.fill pair) = pair :=
  terminalSegal2.fillSpine pair

end FX1Poly.Tier0
