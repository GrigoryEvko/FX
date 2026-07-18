import FX1Poly.Polygraph.TwoCategory.WalkingSemilattice.FiniteSetSemilatticeSeed

/-! # WalkingBooleanAlgebra/BooleanAlgebraSeed — the walking free bounded BOOLEAN ALGEBRA on an ARBITRARY alphabet

The complemented corner of the `n`-colour walker family, the direct successor to the free bounded distributive
lattice (`DistributiveLatticeSeed`, signature `{∧, ∨, ⊤, ⊥}`).  Here the signature gains the unary COMPLEMENT
`¬`, giving the full Boolean-algebra signature `{∧, ∨, ¬, ⊤, ⊥}` closed under the bounded-distributive-lattice
laws PLUS the two complement laws `join a (¬a) ≈ ⊤` and `meet a (¬a) ≈ ⊥`.  Every term now denotes an arbitrary
(not merely monotone) Boolean function of its generators.

## The canonical form: the MINTERM disjunctive normal form

The free Boolean algebra on generators is the finite subalgebra of the two-element algebra `Bool`: two terms
are convertible exactly when they have the same TRUTH TABLE.  Unlike the distributive-lattice sibling — whose
DNF-of-clauses canonical form walled at ⊆-antichain minimization (the clauses form a lattice with a genuine
absorption/minimization confluence problem) — the Boolean MINTERM canonical form has NO antichain problem:
distinct minterms over a fixed generator list are INCOMPARABLE atoms (a minterm fixes the truth value of every
generator, so two distinct minterms meet to `⊥`), and the canonical form is simply the JOIN of the minterms on
which the term evaluates `true`.  A minterm over `gens = [g0, …, g_{k-1}]` and a `mask : List Bool` is the meet
`⋀ᵢ (if maskᵢ then gen gᵢ else ¬ gen gᵢ)`; the minterm-NF of a term is the join over every mask making the term
`true` of that mask's minterm.  Because the true-mask SET is exactly the term's truth table, the minterm-NF is a
faithful canonical representative — so completeness SHOULD be reachable in principle (no minimization wall).

## What this file ships — the SOUND floor, the derived-law richness, and the honest completeness WALL

DECIDED (all zero-axiom):

* **the carrier** `BoolAlgTree` (`gen` / `topOp` / `botOp` / `meetOp` / `joinOp` / `complOp`) and the two-element
  Boolean-algebra evaluation `evalBoolAlgTree` (`∧ = &&`, `∨ = ||`, `¬ = !`, `⊤ = true`, `⊥ = false`);
* **the convertibility** `BooleanAlgebraTreeConv` closed under all the bounded-distributive-lattice laws plus the
  two COMPLEMENT laws, the three congruences `meetCongr` / `joinCongr` / `complCongr`, and `refl` / `symm` /
  `trans`;
* **soundness for the semantic invariant** `booleanAlgebraTreeConv_eval_sound` — convertible trees agree under
  every Boolean environment (each law is a finite `Bool` identity closed by exhaustive `cases … <;> rfl`), a
  GENUINELY SOUND separator that decides non-convertibility;
* **derived-law witnesses showing the convertibility is RICH** — uniqueness of complements
  (`booleanAlgebraComplementUnique`) and DOUBLE COMPLEMENT `¬¬a ≈ a` (`booleanAlgebraDoubleComplement`) are
  GENUINE `BooleanAlgebraTreeConv` derivations from the axioms (double complement via the uniqueness lemma:
  `a` and `¬¬a` are both complements of `¬a`); De Morgan's two laws are stated and proved at the EVALUATION level
  (`booleanAlgebraDeMorganMeet` / `booleanAlgebraDeMorganJoin`, finite `Bool` identities) rather than as Conv
  derivations, because a clean Conv derivation of De Morgan needs the long `(a∧b) ∨ ¬a ∨ ¬b ≈ ⊤` complement chain
  — the route taken is noted per theorem;
* **negative groundings** — distinct generators separate, `⊤ ≠ ⊥`, and (the complement content) a generator is
  NOT convertible to its own complement, each refuted through `evalBoolAlgTree` soundness plus an explicit env;
* **the Shannon cofactor split** `booleanAlgebraCofactorSplit` — `t ≈ (gen c ∧ t) ∨ (¬gen c ∧ t)`, a GENUINE Conv
  derivation (the entry point of minterm normalization), a real partial attempt at completeness;
* **the minterm-DNF scaffolding** — `boolAlgMintermOf` (the meet realizing a mask), `boolAlgConsAll` /
  `boolAlgAllMasks` (all `2ⁿ` Bool-masks, built CONS-ONLY via an accumulator — no `++`), `boolAlgMaskEnv` (the
  environment a mask induces on the generator list), `boolAlgJoinTrueMinterms` / `boolAlgMintermNF` (the join of
  the term's true-minterms), with rfl/count smokes confirming the mask enumeration and the NF computation.

WALLED — the exact blocking node is `fxWalkingBooleanAlgebra_completenessWall` (see its docstring): the minterm
NORMALIZATION lemma `boolAlgConvToMintermNF` (every term Conv-reduces to the join of its true-minterms) resisted;
concretely the generator-substitution-under-meet lemma (its COMPLEMENT case) and the combinatorial assembly
matching the recursive true-minterm join to the semantic true-set are not closed.  The genuinely-undeclared
decision decls (`boolAlgConvToMintermNF`, `booleanAlgebraTreeConv_iff_truthTable`,
`decideBooleanAlgebraTreeConv`) are ABSENT — not sorried, not asserted.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`-on-`Prop`
— the finite `Bool` case-bashing is fully structural (`Bool.rec` + `rfl`), the mask enumeration is cons-only, and
no `List.append` (`++`), `Nat.le`/`Nat.ble` lemma, or `Int` appears anywhere. -/

namespace FX1Poly.Polygraph

/-! ## The bounded-Boolean-algebra tree carrier over a colour alphabet -/

/-- ★ The **tree carrier** of the walking bounded Boolean algebra on an arbitrary alphabet: an un-indexed tree
over colour-indexed generators plus the `{∧, ∨, ¬, ⊤, ⊥}` signature.  `gen colour` is a generator tagged with a
colour in `ℕ`; `topOp` is the nullary `⊤`; `botOp` is the nullary `⊥`; `meetOp` grafts under the binary meet
`∧`; `joinOp` grafts under the binary join `∨`; `complOp` is the unary complement `¬`.  A closed tree's truth
table over its generators is its complete convertibility invariant. -/
inductive BoolAlgTree where
  /-- A generator tagged with a colour in `ℕ` — an element of the chosen alphabet. -/
  | gen (colour : Nat)
  /-- The nullary generator `⊤` (top). -/
  | topOp
  /-- The nullary generator `⊥` (bottom). -/
  | botOp
  /-- The binary meet `∧` grafting the left and right subtrees (`meet(left, right)`). -/
  | meetOp : BoolAlgTree → BoolAlgTree → BoolAlgTree
  /-- The binary join `∨` grafting the left and right subtrees (`join(left, right)`). -/
  | joinOp : BoolAlgTree → BoolAlgTree → BoolAlgTree
  /-- The unary complement `¬` under the subtree (`compl(subtree)`). -/
  | complOp : BoolAlgTree → BoolAlgTree

/-! ## The Boolean evaluation (the sound semantic invariant) -/

/-- **Evaluate a Boolean-algebra tree into the two-element Boolean algebra `Bool`** under a Boolean environment
assigning each colour a truth value: `gen` reads the environment, `topOp ↦ true`, `botOp ↦ false`, `meetOp ↦ &&`,
`joinOp ↦ ||`, `complOp ↦ !` (Boolean negation).  `Bool` under `(&&, ||, !, true, false)` satisfies every
Boolean-algebra law, so this evaluation is a sound convertibility invariant; a full-enumeration structural fold,
propext-clean. -/
def evalBoolAlgTree (env : Nat → Bool) : BoolAlgTree → Bool
  | .gen colour => env colour
  | .topOp => true
  | .botOp => false
  | .meetOp left right => evalBoolAlgTree env left && evalBoolAlgTree env right
  | .joinOp left right => evalBoolAlgTree env left || evalBoolAlgTree env right
  | .complOp subtree => ! evalBoolAlgTree env subtree

/-- Smoke: a generator evaluates to its environment value. -/
theorem evalBoolAlgTree_gen (env : Nat → Bool) (colour : Nat) :
    evalBoolAlgTree env (BoolAlgTree.gen colour) = env colour := rfl

/-- Smoke: meet evaluates to the Boolean conjunction of the children's values. -/
theorem evalBoolAlgTree_meet (env : Nat → Bool) (left right : BoolAlgTree) :
    evalBoolAlgTree env (BoolAlgTree.meetOp left right)
      = (evalBoolAlgTree env left && evalBoolAlgTree env right) := rfl

/-- Smoke: complement evaluates to the Boolean negation of the child's value. -/
theorem evalBoolAlgTree_compl (env : Nat → Bool) (subtree : BoolAlgTree) :
    evalBoolAlgTree env (BoolAlgTree.complOp subtree) = (! evalBoolAlgTree env subtree) := rfl

/-! ## The bounded-Boolean-algebra tree convertibility -/

/-- ★ The **tree convertibility** of the walking bounded Boolean algebra on an arbitrary alphabet — the free
convertibility of the `{∧, ∨, ¬, ⊤, ⊥}` signature over colour-tagged generators closed under the
bounded-distributive-lattice laws (meet and join each associative / commutative / idempotent, the four unit /
absorber laws, the two absorption laws, and both distributivities), the two COMPLEMENT laws (`join a (¬a) ≈ ⊤`
and `meet a (¬a) ≈ ⊥`), the three congruences `meetCongr` / `joinCongr` / `complCongr`, and `refl` / `symm` /
`trans`.  De Morgan and double complement are DERIVED (not constructors).  Two trees denote the same element of
the free bounded Boolean algebra on `ℕ` exactly when they are `BooleanAlgebraTreeConv`-related. -/
inductive BooleanAlgebraTreeConv : BoolAlgTree → BoolAlgTree → Prop where
  /-- **Meet associativity** `meet(meet(left, middle), right) ≈ meet(left, meet(middle, right))`. -/
  | meetAssoc (left middle right : BoolAlgTree) :
      BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp (BoolAlgTree.meetOp left middle) right)
        (BoolAlgTree.meetOp left (BoolAlgTree.meetOp middle right))
  /-- **Meet commutativity** `meet(left, right) ≈ meet(right, left)`. -/
  | meetComm (left right : BoolAlgTree) :
      BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp left right) (BoolAlgTree.meetOp right left)
  /-- **Meet idempotency** `meet(subtree, subtree) ≈ subtree`. -/
  | meetIdem (subtree : BoolAlgTree) :
      BooleanAlgebraTreeConv (BoolAlgTree.meetOp subtree subtree) subtree
  /-- **Join associativity** `join(join(left, middle), right) ≈ join(left, join(middle, right))`. -/
  | joinAssoc (left middle right : BoolAlgTree) :
      BooleanAlgebraTreeConv
        (BoolAlgTree.joinOp (BoolAlgTree.joinOp left middle) right)
        (BoolAlgTree.joinOp left (BoolAlgTree.joinOp middle right))
  /-- **Join commutativity** `join(left, right) ≈ join(right, left)`. -/
  | joinComm (left right : BoolAlgTree) :
      BooleanAlgebraTreeConv
        (BoolAlgTree.joinOp left right) (BoolAlgTree.joinOp right left)
  /-- **Join idempotency** `join(subtree, subtree) ≈ subtree`. -/
  | joinIdem (subtree : BoolAlgTree) :
      BooleanAlgebraTreeConv (BoolAlgTree.joinOp subtree subtree) subtree
  /-- **Meet top unit** `meet(subtree, ⊤) ≈ subtree`. -/
  | meetTop (subtree : BoolAlgTree) :
      BooleanAlgebraTreeConv (BoolAlgTree.meetOp subtree BoolAlgTree.topOp) subtree
  /-- **Join bottom unit** `join(subtree, ⊥) ≈ subtree`. -/
  | joinBot (subtree : BoolAlgTree) :
      BooleanAlgebraTreeConv (BoolAlgTree.joinOp subtree BoolAlgTree.botOp) subtree
  /-- **Meet bottom absorber** `meet(subtree, ⊥) ≈ ⊥`. -/
  | meetBot (subtree : BoolAlgTree) :
      BooleanAlgebraTreeConv (BoolAlgTree.meetOp subtree BoolAlgTree.botOp) BoolAlgTree.botOp
  /-- **Join top absorber** `join(subtree, ⊤) ≈ ⊤`. -/
  | joinTop (subtree : BoolAlgTree) :
      BooleanAlgebraTreeConv (BoolAlgTree.joinOp subtree BoolAlgTree.topOp) BoolAlgTree.topOp
  /-- **Meet absorbs join** `meet(base, join(base, other)) ≈ base`. -/
  | absorbMeetJoin (base other : BoolAlgTree) :
      BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp base (BoolAlgTree.joinOp base other)) base
  /-- **Join absorbs meet** `join(base, meet(base, other)) ≈ base`. -/
  | absorbJoinMeet (base other : BoolAlgTree) :
      BooleanAlgebraTreeConv
        (BoolAlgTree.joinOp base (BoolAlgTree.meetOp base other)) base
  /-- **Meet distributes over join** `meet(factor, join(left, right)) ≈ join(meet(factor, left), meet(factor,
  right))`. -/
  | distribMeetJoin (factor left right : BoolAlgTree) :
      BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp factor (BoolAlgTree.joinOp left right))
        (BoolAlgTree.joinOp (BoolAlgTree.meetOp factor left) (BoolAlgTree.meetOp factor right))
  /-- **Join distributes over meet** `join(factor, meet(left, right)) ≈ meet(join(factor, left), join(factor,
  right))` — the dual distributivity (kept primitive to keep soundness a clean `Bool` identity). -/
  | distribJoinMeet (factor left right : BoolAlgTree) :
      BooleanAlgebraTreeConv
        (BoolAlgTree.joinOp factor (BoolAlgTree.meetOp left right))
        (BoolAlgTree.meetOp (BoolAlgTree.joinOp factor left) (BoolAlgTree.joinOp factor right))
  /-- **Meet complement** `meet(subtree, compl(subtree)) ≈ ⊥` — a value and its complement meet to bottom. -/
  | meetCompl (subtree : BoolAlgTree) :
      BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp subtree (BoolAlgTree.complOp subtree)) BoolAlgTree.botOp
  /-- **Join complement** `join(subtree, compl(subtree)) ≈ ⊤` — a value and its complement join to top. -/
  | joinCompl (subtree : BoolAlgTree) :
      BooleanAlgebraTreeConv
        (BoolAlgTree.joinOp subtree (BoolAlgTree.complOp subtree)) BoolAlgTree.topOp
  /-- **Congruence under a meet node** — into BOTH children. -/
  | meetCongr {leftOld leftNew rightOld rightNew : BoolAlgTree} :
      BooleanAlgebraTreeConv leftOld leftNew → BooleanAlgebraTreeConv rightOld rightNew →
      BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp leftOld rightOld) (BoolAlgTree.meetOp leftNew rightNew)
  /-- **Congruence under a join node** — into BOTH children. -/
  | joinCongr {leftOld leftNew rightOld rightNew : BoolAlgTree} :
      BooleanAlgebraTreeConv leftOld leftNew → BooleanAlgebraTreeConv rightOld rightNew →
      BooleanAlgebraTreeConv
        (BoolAlgTree.joinOp leftOld rightOld) (BoolAlgTree.joinOp leftNew rightNew)
  /-- **Congruence under a complement node**. -/
  | complCongr {subtreeOld subtreeNew : BoolAlgTree} :
      BooleanAlgebraTreeConv subtreeOld subtreeNew →
      BooleanAlgebraTreeConv (BoolAlgTree.complOp subtreeOld) (BoolAlgTree.complOp subtreeNew)
  /-- Reflexivity. -/
  | refl (tree : BoolAlgTree) : BooleanAlgebraTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : BoolAlgTree} :
      BooleanAlgebraTreeConv tree1 tree2 → BooleanAlgebraTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : BoolAlgTree} :
      BooleanAlgebraTreeConv tree1 tree2 → BooleanAlgebraTreeConv tree2 tree3 →
      BooleanAlgebraTreeConv tree1 tree3

/-! ## Soundness for the Boolean evaluation -/

/-- ★ **Soundness for the semantic invariant** — convertible trees agree under EVERY Boolean environment.  Each
law maps to a finite `Bool` identity closed by exhaustive case analysis on the children's Boolean values (meet
`= &&`, join `= ||`, compl `= !`, top `= true`, bottom `= false`); the two complement laws case on the single
child; the three congruences rewrite by the inductive hypotheses; `refl` / `symm` / `trans` are `rfl` / `.symm` /
`.trans`.  Because `Bool` is a bounded Boolean algebra, this evaluation is a GENUINELY SOUND convertibility
invariant — it decides non-convertibility (used by the negative groundings).  All `Bool` reasoning is
propext-clean (`Bool.rec` + `rfl`, no `decide`-on-`Prop`). -/
theorem booleanAlgebraTreeConv_eval_sound {source target : BoolAlgTree}
    (conv : BooleanAlgebraTreeConv source target) :
    ∀ env : Nat → Bool, evalBoolAlgTree env source = evalBoolAlgTree env target := by
  induction conv with
  | meetAssoc left middle right =>
    intro env
    show ((evalBoolAlgTree env left && evalBoolAlgTree env middle) && evalBoolAlgTree env right)
      = (evalBoolAlgTree env left && (evalBoolAlgTree env middle && evalBoolAlgTree env right))
    cases evalBoolAlgTree env left <;> cases evalBoolAlgTree env middle <;>
      cases evalBoolAlgTree env right <;> rfl
  | meetComm left right =>
    intro env
    show (evalBoolAlgTree env left && evalBoolAlgTree env right)
      = (evalBoolAlgTree env right && evalBoolAlgTree env left)
    cases evalBoolAlgTree env left <;> cases evalBoolAlgTree env right <;> rfl
  | meetIdem subtree =>
    intro env
    show (evalBoolAlgTree env subtree && evalBoolAlgTree env subtree) = evalBoolAlgTree env subtree
    cases evalBoolAlgTree env subtree <;> rfl
  | joinAssoc left middle right =>
    intro env
    show ((evalBoolAlgTree env left || evalBoolAlgTree env middle) || evalBoolAlgTree env right)
      = (evalBoolAlgTree env left || (evalBoolAlgTree env middle || evalBoolAlgTree env right))
    cases evalBoolAlgTree env left <;> cases evalBoolAlgTree env middle <;>
      cases evalBoolAlgTree env right <;> rfl
  | joinComm left right =>
    intro env
    show (evalBoolAlgTree env left || evalBoolAlgTree env right)
      = (evalBoolAlgTree env right || evalBoolAlgTree env left)
    cases evalBoolAlgTree env left <;> cases evalBoolAlgTree env right <;> rfl
  | joinIdem subtree =>
    intro env
    show (evalBoolAlgTree env subtree || evalBoolAlgTree env subtree) = evalBoolAlgTree env subtree
    cases evalBoolAlgTree env subtree <;> rfl
  | meetTop subtree =>
    intro env
    show (evalBoolAlgTree env subtree && true) = evalBoolAlgTree env subtree
    cases evalBoolAlgTree env subtree <;> rfl
  | joinBot subtree =>
    intro env
    show (evalBoolAlgTree env subtree || false) = evalBoolAlgTree env subtree
    cases evalBoolAlgTree env subtree <;> rfl
  | meetBot subtree =>
    intro env
    show (evalBoolAlgTree env subtree && false) = false
    cases evalBoolAlgTree env subtree <;> rfl
  | joinTop subtree =>
    intro env
    show (evalBoolAlgTree env subtree || true) = true
    cases evalBoolAlgTree env subtree <;> rfl
  | absorbMeetJoin base other =>
    intro env
    show (evalBoolAlgTree env base && (evalBoolAlgTree env base || evalBoolAlgTree env other))
      = evalBoolAlgTree env base
    cases evalBoolAlgTree env base <;> cases evalBoolAlgTree env other <;> rfl
  | absorbJoinMeet base other =>
    intro env
    show (evalBoolAlgTree env base || (evalBoolAlgTree env base && evalBoolAlgTree env other))
      = evalBoolAlgTree env base
    cases evalBoolAlgTree env base <;> cases evalBoolAlgTree env other <;> rfl
  | distribMeetJoin factor left right =>
    intro env
    show (evalBoolAlgTree env factor && (evalBoolAlgTree env left || evalBoolAlgTree env right))
      = ((evalBoolAlgTree env factor && evalBoolAlgTree env left)
        || (evalBoolAlgTree env factor && evalBoolAlgTree env right))
    cases evalBoolAlgTree env factor <;> cases evalBoolAlgTree env left <;>
      cases evalBoolAlgTree env right <;> rfl
  | distribJoinMeet factor left right =>
    intro env
    show (evalBoolAlgTree env factor || (evalBoolAlgTree env left && evalBoolAlgTree env right))
      = ((evalBoolAlgTree env factor || evalBoolAlgTree env left)
        && (evalBoolAlgTree env factor || evalBoolAlgTree env right))
    cases evalBoolAlgTree env factor <;> cases evalBoolAlgTree env left <;>
      cases evalBoolAlgTree env right <;> rfl
  | meetCompl subtree =>
    intro env
    show (evalBoolAlgTree env subtree && ! evalBoolAlgTree env subtree) = false
    cases evalBoolAlgTree env subtree <;> rfl
  | joinCompl subtree =>
    intro env
    show (evalBoolAlgTree env subtree || ! evalBoolAlgTree env subtree) = true
    cases evalBoolAlgTree env subtree <;> rfl
  | @meetCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
    intro env
    show (evalBoolAlgTree env leftOld && evalBoolAlgTree env rightOld)
      = (evalBoolAlgTree env leftNew && evalBoolAlgTree env rightNew)
    rw [ihLeft env, ihRight env]
  | @joinCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
    intro env
    show (evalBoolAlgTree env leftOld || evalBoolAlgTree env rightOld)
      = (evalBoolAlgTree env leftNew || evalBoolAlgTree env rightNew)
    rw [ihLeft env, ihRight env]
  | @complCongr subtreeOld subtreeNew _ ih =>
    intro env
    show (! evalBoolAlgTree env subtreeOld) = (! evalBoolAlgTree env subtreeNew)
    rw [ih env]
  | refl tree => intro env; rfl
  | symm _ ih => intro env; exact (ih env).symm
  | trans _ _ ihAB ihBC => intro env; exact (ihAB env).trans (ihBC env)

/-! ## Derived-law witnesses (the convertibility is RICH) -/

/-- ★ **Uniqueness of complements** — in a bounded distributive lattice with complements, an element has AT MOST
one complement.  If `x` and `y` are both complements of `elem` (each joins with `elem` to `⊤` and meets with
`elem` to `⊥`), then `x ≈ y`.  Proof: `x ≈ x ∧ ⊤ ≈ x ∧ (elem ∨ y) ≈ (x ∧ elem) ∨ (x ∧ y) ≈ ⊥ ∨ (x ∧ y) ≈ x ∧ y`,
and symmetrically `y ≈ x ∧ y`, so `x ≈ y`.  A genuine `BooleanAlgebraTreeConv` derivation — the engine behind
double complement and (were it pushed) De Morgan. -/
theorem booleanAlgebraComplementUnique {elem tree1 tree2 : BoolAlgTree}
    (hJoin1 : BooleanAlgebraTreeConv (BoolAlgTree.joinOp elem tree1) BoolAlgTree.topOp)
    (hMeet1 : BooleanAlgebraTreeConv (BoolAlgTree.meetOp elem tree1) BoolAlgTree.botOp)
    (hJoin2 : BooleanAlgebraTreeConv (BoolAlgTree.joinOp elem tree2) BoolAlgTree.topOp)
    (hMeet2 : BooleanAlgebraTreeConv (BoolAlgTree.meetOp elem tree2) BoolAlgTree.botOp) :
    BooleanAlgebraTreeConv tree1 tree2 := by
  have hFirst : BooleanAlgebraTreeConv tree1 (BoolAlgTree.meetOp tree1 tree2) :=
    (BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.meetTop tree1)).trans
      ((BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl tree1)
          (BooleanAlgebraTreeConv.symm hJoin2)).trans
        ((BooleanAlgebraTreeConv.distribMeetJoin tree1 elem tree2).trans
          ((BooleanAlgebraTreeConv.joinCongr (BooleanAlgebraTreeConv.meetComm tree1 elem)
              (BooleanAlgebraTreeConv.refl (BoolAlgTree.meetOp tree1 tree2))).trans
            ((BooleanAlgebraTreeConv.joinCongr hMeet1
                (BooleanAlgebraTreeConv.refl (BoolAlgTree.meetOp tree1 tree2))).trans
              ((BooleanAlgebraTreeConv.joinComm BoolAlgTree.botOp (BoolAlgTree.meetOp tree1 tree2)).trans
                (BooleanAlgebraTreeConv.joinBot (BoolAlgTree.meetOp tree1 tree2)))))))
  have hSecond : BooleanAlgebraTreeConv tree2 (BoolAlgTree.meetOp tree1 tree2) :=
    (BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.meetTop tree2)).trans
      ((BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl tree2)
          (BooleanAlgebraTreeConv.symm hJoin1)).trans
        ((BooleanAlgebraTreeConv.distribMeetJoin tree2 elem tree1).trans
          ((BooleanAlgebraTreeConv.joinCongr (BooleanAlgebraTreeConv.meetComm tree2 elem)
              (BooleanAlgebraTreeConv.refl (BoolAlgTree.meetOp tree2 tree1))).trans
            ((BooleanAlgebraTreeConv.joinCongr hMeet2
                (BooleanAlgebraTreeConv.refl (BoolAlgTree.meetOp tree2 tree1))).trans
              ((BooleanAlgebraTreeConv.joinComm BoolAlgTree.botOp (BoolAlgTree.meetOp tree2 tree1)).trans
                ((BooleanAlgebraTreeConv.joinBot (BoolAlgTree.meetOp tree2 tree1)).trans
                  (BooleanAlgebraTreeConv.meetComm tree2 tree1)))))))
  exact hFirst.trans (BooleanAlgebraTreeConv.symm hSecond)

/-- ★ **Double complement** `¬¬a ≈ a` — a GENUINE `BooleanAlgebraTreeConv` derivation.  Both `a` and `¬¬a` are
complements of `¬a`: `¬a ∨ ¬¬a ≈ ⊤` and `¬a ∧ ¬¬a ≈ ⊥` are the complement laws for `¬a`, while `¬a ∨ a ≈ ⊤` and
`¬a ∧ a ≈ ⊥` are the complement laws for `a` read through commutativity — so `booleanAlgebraComplementUnique`
identifies them.  (Route: genuine Conv, not eval-level.) -/
theorem booleanAlgebraDoubleComplement (a : BoolAlgTree) :
    BooleanAlgebraTreeConv (BoolAlgTree.complOp (BoolAlgTree.complOp a)) a := by
  refine booleanAlgebraComplementUnique (elem := BoolAlgTree.complOp a) ?_ ?_ ?_ ?_
  · exact BooleanAlgebraTreeConv.joinCompl (BoolAlgTree.complOp a)
  · exact BooleanAlgebraTreeConv.meetCompl (BoolAlgTree.complOp a)
  · exact (BooleanAlgebraTreeConv.joinComm (BoolAlgTree.complOp a) a).trans
      (BooleanAlgebraTreeConv.joinCompl a)
  · exact (BooleanAlgebraTreeConv.meetComm (BoolAlgTree.complOp a) a).trans
      (BooleanAlgebraTreeConv.meetCompl a)

/-- ★ **De Morgan (meet)** `¬(a ∧ b) ≈ ¬a ∨ ¬b` at the EVALUATION level — for every environment,
`!(eval a && eval b) = (!eval a) || (!eval b)`, a finite `Bool` identity closed by `cases … <;> rfl`.  (Route:
eval-level, not Conv — the genuine Conv derivation needs the long `(a∧b) ∨ ¬a ∨ ¬b ≈ ⊤` complement chain via
`booleanAlgebraComplementUnique`.) -/
theorem booleanAlgebraDeMorganMeet (a b : BoolAlgTree) (env : Nat → Bool) :
    evalBoolAlgTree env (BoolAlgTree.complOp (BoolAlgTree.meetOp a b))
      = evalBoolAlgTree env (BoolAlgTree.joinOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)) := by
  show (! (evalBoolAlgTree env a && evalBoolAlgTree env b))
    = ((! evalBoolAlgTree env a) || (! evalBoolAlgTree env b))
  cases evalBoolAlgTree env a <;> cases evalBoolAlgTree env b <;> rfl

/-- ★ **De Morgan (join)** `¬(a ∨ b) ≈ ¬a ∧ ¬b` at the EVALUATION level — the dual, `!(eval a || eval b) =
(!eval a) && (!eval b)`, by `cases … <;> rfl`.  (Route: eval-level, as for the meet dual.) -/
theorem booleanAlgebraDeMorganJoin (a b : BoolAlgTree) (env : Nat → Bool) :
    evalBoolAlgTree env (BoolAlgTree.complOp (BoolAlgTree.joinOp a b))
      = evalBoolAlgTree env (BoolAlgTree.meetOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)) := by
  show (! (evalBoolAlgTree env a || evalBoolAlgTree env b))
    = ((! evalBoolAlgTree env a) && (! evalBoolAlgTree env b))
  cases evalBoolAlgTree env a <;> cases evalBoolAlgTree env b <;> rfl

/-! ## The Shannon cofactor split (the entry point of minterm normalization) -/

/-- ★ **The Shannon cofactor split** — `t ≈ (gen c ∧ t) ∨ (¬gen c ∧ t)`, a GENUINE `BooleanAlgebraTreeConv`
derivation: `t ≈ t ∧ ⊤ ≈ t ∧ (gen c ∨ ¬gen c) ≈ (t ∧ gen c) ∨ (t ∧ ¬gen c) ≈ (gen c ∧ t) ∨ (¬gen c ∧ t)` via
`meetTop`, `joinCompl`, `distribMeetJoin`, and two `meetComm`s.  The first step of the minterm expansion (peel one
generator); a real partial attempt at the walled completeness. -/
theorem booleanAlgebraCofactorSplit (colour : Nat) (tree : BoolAlgTree) :
    BooleanAlgebraTreeConv tree
      (BoolAlgTree.joinOp
        (BoolAlgTree.meetOp (BoolAlgTree.gen colour) tree)
        (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen colour)) tree)) :=
  (BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.meetTop tree)).trans
    ((BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl tree)
        (BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.joinCompl (BoolAlgTree.gen colour)))).trans
      ((BooleanAlgebraTreeConv.distribMeetJoin tree (BoolAlgTree.gen colour)
          (BoolAlgTree.complOp (BoolAlgTree.gen colour))).trans
        (BooleanAlgebraTreeConv.joinCongr
          (BooleanAlgebraTreeConv.meetComm tree (BoolAlgTree.gen colour))
          (BooleanAlgebraTreeConv.meetComm tree (BoolAlgTree.complOp (BoolAlgTree.gen colour))))))

/-! ## Negative groundings (refuted through the Boolean soundness) -/

/-- ★ **The decision in action (negative, distinct generators)** — `gen 0` is NOT convertible to `gen 1`: the
environment `fun colour => Nat.beq colour 0` sends colour `0 ↦ true` and colour `1 ↦ false`, so by
`evalBoolAlgTree` soundness no convertibility can exist.  `Bool.noConfusion`. -/
theorem booleanAlgebraSeparatesGenerators :
    ¬ BooleanAlgebraTreeConv (BoolAlgTree.gen 0) (BoolAlgTree.gen 1) := by
  intro conv
  have hEval := booleanAlgebraTreeConv_eval_sound conv (fun colour => Nat.beq colour 0)
  have hAbsurd : (true : Bool) = false := hEval
  exact Bool.noConfusion hAbsurd

/-- ★ **The decision in action (negative, `⊤ ≠ ⊥`)** — `topOp` is NOT convertible to `botOp`: under any
environment `⊤` evaluates to `true` and `⊥` to `false`.  `Bool.noConfusion`. -/
theorem booleanAlgebraSeparatesTopBot :
    ¬ BooleanAlgebraTreeConv BoolAlgTree.topOp BoolAlgTree.botOp := by
  intro conv
  have hEval := booleanAlgebraTreeConv_eval_sound conv (fun _ => false)
  have hAbsurd : (true : Bool) = false := hEval
  exact Bool.noConfusion hAbsurd

/-- ★ **The decision in action (negative, complement content)** — `gen 0` is NOT convertible to `compl(gen 0)`:
under the constant-`true` environment `gen 0` evaluates to `true` while `¬gen 0` evaluates to `!true = false`, so
by soundness they separate.  This is the complement content the distributive-lattice walker structurally cannot
see.  `Bool.noConfusion`. -/
theorem booleanAlgebraComplementNontrivial :
    ¬ BooleanAlgebraTreeConv (BoolAlgTree.gen 0) (BoolAlgTree.complOp (BoolAlgTree.gen 0)) := by
  intro conv
  have hEval := booleanAlgebraTreeConv_eval_sound conv (fun _ => true)
  have hAbsurd : (true : Bool) = false := hEval
  exact Bool.noConfusion hAbsurd

/-! ## The minterm-DNF scaffolding (computes, zero-axiom) -/

/-- The **length** of a generator list — a purpose-built structural count (avoiding any `List.length` axiom
surprise), the parameter to the mask enumeration. -/
def boolAlgGensLength : List Nat → Nat
  | [] => 0
  | _ :: tail => Nat.succ (boolAlgGensLength tail)

/-- ★ The **minterm realizing a mask** over a generator list: the meet, generator by generator in lockstep with
the mask, of `gen gᵢ` when `maskᵢ = true` and `compl(gen gᵢ)` when `maskᵢ = false`, terminating at `topOp` (the
empty meet) when either list runs out.  A minterm fixes the truth value of every listed generator. -/
def boolAlgMintermOf : List Nat → List Bool → BoolAlgTree
  | [], _ => BoolAlgTree.topOp
  | _ :: _, [] => BoolAlgTree.topOp
  | generator :: generators, bit :: bits =>
      BoolAlgTree.meetOp
        (match bit with
         | true => BoolAlgTree.gen generator
         | false => BoolAlgTree.complOp (BoolAlgTree.gen generator))
        (boolAlgMintermOf generators bits)

/-- **Prepend a bit to every mask** of a mask-list and cons the results onto an accumulator — a cons-only
`map (bit :: ·)` fused with the accumulator so the mask enumeration never calls `List.append`. -/
def boolAlgConsAll (bit : Bool) : List (List Bool) → List (List Bool) → List (List Bool)
  | [], acc => acc
  | mask :: masks, acc => (bit :: mask) :: boolAlgConsAll bit masks acc

/-- ★ **All `2ⁿ` Boolean masks of length `n`** — built CONS-ONLY: `allMasks 0 = [[]]`, and `allMasks (n+1)` is
every length-`n` mask prefixed by `false` (via `boolAlgConsAll false`) followed by every one prefixed by `true`
(via `boolAlgConsAll true`), threaded through an accumulator so no `++` is used. -/
def boolAlgAllMasks : Nat → List (List Bool)
  | 0 => [[]]
  | Nat.succ n =>
      boolAlgConsAll false (boolAlgAllMasks n) (boolAlgConsAll true (boolAlgAllMasks n) [])

/-- ★ The **environment a mask induces on a generator list** — reads the truth value of a colour by looking it up
in the generator list (via the core `Nat.beq`) and returning the corresponding mask bit, defaulting to `false`
for any colour outside the list.  A cons-only lockstep lookup. -/
def boolAlgMaskEnv : List Nat → List Bool → Nat → Bool
  | [], _, _ => false
  | _ :: _, [], _ => false
  | generator :: generators, bit :: bits, colour =>
      match Nat.beq colour generator with
      | true => bit
      | false => boolAlgMaskEnv generators bits colour

/-- **Join the true-minterms** over a mask-list: for each mask, if the tree evaluates to `true` under the mask's
environment, join in that mask's minterm; otherwise skip.  `botOp` (the empty join) at the end. -/
def boolAlgJoinTrueMinterms (gens : List Nat) (tree : BoolAlgTree) : List (List Bool) → BoolAlgTree
  | [] => BoolAlgTree.botOp
  | mask :: rest =>
      match evalBoolAlgTree (boolAlgMaskEnv gens mask) tree with
      | true =>
          BoolAlgTree.joinOp (boolAlgMintermOf gens mask) (boolAlgJoinTrueMinterms gens tree rest)
      | false => boolAlgJoinTrueMinterms gens tree rest

/-- ★ The **minterm disjunctive normal form** of a tree over a generator list: the join, over every mask in
`boolAlgAllMasks (boolAlgGensLength gens)` making the tree evaluate `true`, of that mask's minterm.  The true-mask
SET is exactly the tree's truth table over `gens`, so this is the canonical representative — the target of the
(walled) normalization lemma `boolAlgConvToMintermNF`. -/
def boolAlgMintermNF (gens : List Nat) (tree : BoolAlgTree) : BoolAlgTree :=
  boolAlgJoinTrueMinterms gens tree (boolAlgAllMasks (boolAlgGensLength gens))

/-! ## Scaffolding smokes — the mask enumeration and NF compute -/

/-- Smoke (count): the length-`0` mask enumeration is the single empty mask (`2⁰ = 1`). -/
theorem boolAlgAllMasks_zero : boolAlgAllMasks 0 = [[]] := rfl

/-- Smoke (count): the length-`1` mask enumeration is the two masks `[false]`, `[true]` (`2¹ = 2`). -/
theorem boolAlgAllMasks_one : boolAlgAllMasks 1 = [[false], [true]] := rfl

/-- Smoke (count): the length-`2` mask enumeration is the four masks, in `false`-prefixed then `true`-prefixed
order (`2² = 4`). -/
theorem boolAlgAllMasks_two :
    boolAlgAllMasks 2 = [[false, false], [false, true], [true, false], [true, true]] := rfl

/-- Smoke: the all-`true` minterm over `[0]` is `meet(gen 0, ⊤)`. -/
theorem boolAlgMintermOf_smoke :
    boolAlgMintermOf [0] [true] = BoolAlgTree.meetOp (BoolAlgTree.gen 0) BoolAlgTree.topOp := rfl

/-- Smoke: a mixed minterm over `[0, 1]` with mask `[true, false]` is
`meet(gen 0, meet(compl(gen 1), ⊤))` — the `true` bit contributes the generator, the `false` bit its
complement. -/
theorem boolAlgMintermOf_smokeTwo :
    boolAlgMintermOf [0, 1] [true, false]
      = BoolAlgTree.meetOp (BoolAlgTree.gen 0)
          (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen 1)) BoolAlgTree.topOp) := rfl

/-- Smoke: the minterm-NF of `gen 0` over `[0]` keeps only the `true`-mask minterm — `join(meet(gen 0, ⊤), ⊥)` —
the `false`-mask minterm dropped because `gen 0` evaluates `false` there. -/
theorem boolAlgMintermNF_smoke :
    boolAlgMintermNF [0] (BoolAlgTree.gen 0)
      = BoolAlgTree.joinOp (BoolAlgTree.meetOp (BoolAlgTree.gen 0) BoolAlgTree.topOp) BoolAlgTree.botOp :=
  rfl

/-- Smoke (eval-faithfulness on a grounding): the minterm-NF of `gen 0` over `[0]` agrees with `gen 0` under
every environment — `(eval (gen 0) && true) || false = eval (gen 0)`, by `cases … <;> rfl`.  (The GENERAL
statement — the NF always agrees, i.e. normalization — is the walled node below.) -/
theorem boolAlgMintermNF_eval_gen (env : Nat → Bool) :
    evalBoolAlgTree env (boolAlgMintermNF [0] (BoolAlgTree.gen 0))
      = evalBoolAlgTree env (BoolAlgTree.gen 0) := by
  rw [boolAlgMintermNF_smoke]
  show ((evalBoolAlgTree env (BoolAlgTree.gen 0) && true) || false)
    = evalBoolAlgTree env (BoolAlgTree.gen 0)
  cases evalBoolAlgTree env (BoolAlgTree.gen 0) <;> rfl

/-! ## The wall marker -/

/-- ★ **The walking bounded Boolean algebra on an ARBITRARY alphabet — the SOUND floor and minterm scaffolding
are SHIPPED, but the minterm-NORMALIZATION lemma is WALLED.**  `= false` records the honest state:

* LANDED (zero-axiom): the `BoolAlgTree` carrier, the `Bool` evaluation `evalBoolAlgTree`, the
  `BooleanAlgebraTreeConv` convertibility (bounded-distributive-lattice laws + the two COMPLEMENT laws + the
  three congruences), `booleanAlgebraTreeConv_eval_sound` (a genuine sound separator deciding NON-convertibility),
  the derived-law richness (`booleanAlgebraComplementUnique` + genuine-Conv `booleanAlgebraDoubleComplement`, and
  eval-level `booleanAlgebraDeMorganMeet` / `booleanAlgebraDeMorganJoin`), the distinct-generator / `⊤ ≠ ⊥` /
  generator-vs-complement negative groundings, the genuine-Conv Shannon cofactor split
  `booleanAlgebraCofactorSplit`, and the complete minterm-DNF scaffolding `boolAlgGensLength` /
  `boolAlgMintermOf` / `boolAlgConsAll` / `boolAlgAllMasks` / `boolAlgMaskEnv` / `boolAlgJoinTrueMinterms` /
  `boolAlgMintermNF` (computing the canonical form, with mask-count and NF smokes).

* WALLED — the exact blocking node: the minterm NORMALIZATION lemma `boolAlgConvToMintermNF` — that EVERY term
  with support `⊆ gens` is `BooleanAlgebraTreeConv`-equal to `boolAlgMintermNF gens t`, the join of its
  true-minterms.  The cofactor split (`booleanAlgebraCofactorSplit`) peels one generator, but iterating it to a
  minterm needs a generator-SUBSTITUTION-under-meet lemma `meet (gen c) t ≈ meet (gen c) (t[c := ⊤])` whose
  COMPLEMENT case `meet (gen c) (compl u) ≈ meet (gen c) (compl (u[c := ⊤]))` does not follow from a congruence
  (it needs the restriction argument `gen c ∧ ¬u ≈ gen c ∧ ¬u ∧ (u' ∨ ¬u') ≈ …`, applying the IH both ways),
  plus a combinatorial assembly matching the recursive `boolAlgJoinTrueMinterms` true-set to the term's semantic
  truth table.  Those two are the analogue of the sibling's confluence wall and are NOT closed here; the decision
  decls `boolAlgConvToMintermNF`, `booleanAlgebraTreeConv_iff_truthTable`, and `decideBooleanAlgebraTreeConv` are
  left UNDECLARED (not sorried, not asserted).

All landed declarations are zero-axiom: the finite `Bool` case-bashing is structural (`Bool.rec` + `rfl`), the
mask enumeration is cons-only, and no `List.append` (`++`), `Nat.le`/`Nat.ble` lemma, or `Int` appears
anywhere. -/
def fxWalkingBooleanAlgebra_completenessWall : Bool := false

end FX1Poly.Polygraph
