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

## What this file ships — the SOUND floor, the derived-law richness, and the COMPLETE truth-table DECISION

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
  `a` and `¬¬a` are both complements of `¬a`); De Morgan's two laws are now ALSO Conv-level derivations
  (`booleanAlgebraDeMorganMeetConv` via `booleanAlgebraComplementUnique` on the `(a∧b) ∨ ¬a ∨ ¬b ≈ ⊤` chain, and
  `booleanAlgebraDeMorganJoinConv` from it by double complement), alongside the earlier eval-level versions;
* **negative groundings** — distinct generators separate, `⊤ ≠ ⊥`, and (the complement content) a generator is
  NOT convertible to its own complement, each refuted through `evalBoolAlgTree` soundness plus an explicit env;
* **the Shannon cofactor split** `booleanAlgebraCofactorSplit` — `t ≈ (gen c ∧ t) ∨ (¬gen c ∧ t)`, promoted to the
  **full cofactor decomposition** `boolAlgFullShannon` (`t ≈ (gen c ∧ t[c:=⊤]) ∨ (¬gen c ∧ t[c:=⊥])`) through the
  crux paired double inductions `boolAlgGenRestrictTopPair` / `boolAlgGenRestrictBotPair`;
* **THE COMPLETE TRUTH-TABLE DECISION** — `decideBooleanAlgebraTreeConv` (a terminating `Bool` procedure, a
  recursive Shannon peel over the union colour list `boolAlgDecideOnGens`), the full biconditional
  `booleanAlgebraTreeConv_iff_truthTable` (`s ≈ t ↔ decider s t = true`), and the `Decidable` instance: two trees
  are convertible in the free bounded Boolean algebra on `ℕ` EXACTLY when they have the same truth table — the
  completeness the file previously walled at, now closed;
* **the minterm-DNF scaffolding** (retained as an alternative canonical form, independent of the decision above) —
  `boolAlgMintermOf`, `boolAlgConsAll` / `boolAlgAllMasks` (all `2ⁿ` masks, cons-only), `boolAlgMaskEnv`,
  `boolAlgJoinTrueMinterms` / `boolAlgMintermNF`, with rfl/count smokes.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`-on-`Prop`
— the finite `Bool` case-bashing is fully structural (`Bool.rec` + `rfl`), the substitution/support machinery
recurses structurally, the list plumbing is cons-only, and no `List.append` (`++`), `Nat.le`/`Nat.ble` lemma, or
`Int` appears anywhere. -/

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

/-! ## De Morgan at the convertibility level (via complement uniqueness) -/

/-- `¬⊤ ≈ ⊥` — a genuine `BooleanAlgebraTreeConv` derivation: `¬⊤ ≈ ¬⊤ ∧ ⊤ ≈ ⊤ ∧ ¬⊤ ≈ ⊥`. -/
theorem boolAlgComplTop :
    BooleanAlgebraTreeConv (BoolAlgTree.complOp BoolAlgTree.topOp) BoolAlgTree.botOp :=
  (BooleanAlgebraTreeConv.symm
      (BooleanAlgebraTreeConv.meetTop (BoolAlgTree.complOp BoolAlgTree.topOp))).trans
    ((BooleanAlgebraTreeConv.meetComm (BoolAlgTree.complOp BoolAlgTree.topOp) BoolAlgTree.topOp).trans
      (BooleanAlgebraTreeConv.meetCompl BoolAlgTree.topOp))

/-- `¬⊥ ≈ ⊤` — the dual: `¬⊥ ≈ ¬⊥ ∨ ⊥ ≈ ⊥ ∨ ¬⊥ ≈ ⊤`. -/
theorem boolAlgComplBot :
    BooleanAlgebraTreeConv (BoolAlgTree.complOp BoolAlgTree.botOp) BoolAlgTree.topOp :=
  (BooleanAlgebraTreeConv.symm
      (BooleanAlgebraTreeConv.joinBot (BoolAlgTree.complOp BoolAlgTree.botOp))).trans
    ((BooleanAlgebraTreeConv.joinComm (BoolAlgTree.complOp BoolAlgTree.botOp) BoolAlgTree.botOp).trans
      (BooleanAlgebraTreeConv.joinCompl BoolAlgTree.botOp))

/-- Meet middle-swap `(a∧b)∧(x∧y) ≈ (a∧x)∧(b∧y)` — pure meet-semilattice rearrangement by
associativity and commutativity, used to distribute an idempotent meet-context over a child meet. -/
theorem boolAlgMeetMiddleSwap (a b x y : BoolAlgTree) :
    BooleanAlgebraTreeConv
      (BoolAlgTree.meetOp (BoolAlgTree.meetOp a b) (BoolAlgTree.meetOp x y))
      (BoolAlgTree.meetOp (BoolAlgTree.meetOp a x) (BoolAlgTree.meetOp b y)) := by
  have s1 : BooleanAlgebraTreeConv
      (BoolAlgTree.meetOp (BoolAlgTree.meetOp a b) (BoolAlgTree.meetOp x y))
      (BoolAlgTree.meetOp a (BoolAlgTree.meetOp b (BoolAlgTree.meetOp x y))) :=
    BooleanAlgebraTreeConv.meetAssoc a b (BoolAlgTree.meetOp x y)
  have s2 : BooleanAlgebraTreeConv
      (BoolAlgTree.meetOp a (BoolAlgTree.meetOp b (BoolAlgTree.meetOp x y)))
      (BoolAlgTree.meetOp a (BoolAlgTree.meetOp (BoolAlgTree.meetOp b x) y)) :=
    BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl a)
      (BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.meetAssoc b x y))
  have s3 : BooleanAlgebraTreeConv
      (BoolAlgTree.meetOp a (BoolAlgTree.meetOp (BoolAlgTree.meetOp b x) y))
      (BoolAlgTree.meetOp a (BoolAlgTree.meetOp (BoolAlgTree.meetOp x b) y)) :=
    BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl a)
      (BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.meetComm b x)
        (BooleanAlgebraTreeConv.refl y))
  have s4 : BooleanAlgebraTreeConv
      (BoolAlgTree.meetOp a (BoolAlgTree.meetOp (BoolAlgTree.meetOp x b) y))
      (BoolAlgTree.meetOp a (BoolAlgTree.meetOp x (BoolAlgTree.meetOp b y))) :=
    BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl a)
      (BooleanAlgebraTreeConv.meetAssoc x b y)
  have s5 : BooleanAlgebraTreeConv
      (BoolAlgTree.meetOp a (BoolAlgTree.meetOp x (BoolAlgTree.meetOp b y)))
      (BoolAlgTree.meetOp (BoolAlgTree.meetOp a x) (BoolAlgTree.meetOp b y)) :=
    BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.meetAssoc a x (BoolAlgTree.meetOp b y))
  exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

/-- ★ **De Morgan (meet) at the convertibility level** `¬(a∧b) ≈ ¬a ∨ ¬b` — a GENUINE
`BooleanAlgebraTreeConv` derivation via `booleanAlgebraComplementUnique`: both `¬(a∧b)` and `¬a ∨ ¬b`
are complements of `a∧b`.  The two nontrivial premises are the complement chains `(a∧b) ∨ (¬a ∨ ¬b) ≈ ⊤`
and `(a∧b) ∧ (¬a ∨ ¬b) ≈ ⊥`.  This is the Conv-level De Morgan the eval-level `booleanAlgebraDeMorganMeet`
noted as needing the long chain — now discharged. -/
theorem booleanAlgebraDeMorganMeetConv (a b : BoolAlgTree) :
    BooleanAlgebraTreeConv (BoolAlgTree.complOp (BoolAlgTree.meetOp a b))
      (BoolAlgTree.joinOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)) := by
  refine booleanAlgebraComplementUnique (elem := BoolAlgTree.meetOp a b) ?_ ?_ ?_ ?_
  · exact BooleanAlgebraTreeConv.joinCompl (BoolAlgTree.meetOp a b)
  · exact BooleanAlgebraTreeConv.meetCompl (BoolAlgTree.meetOp a b)
  · have hassoc : BooleanAlgebraTreeConv
        (BoolAlgTree.joinOp (BoolAlgTree.meetOp a b)
          (BoolAlgTree.joinOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)))
        (BoolAlgTree.joinOp (BoolAlgTree.joinOp (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp a))
          (BoolAlgTree.complOp b)) :=
      BooleanAlgebraTreeConv.symm
        (BooleanAlgebraTreeConv.joinAssoc (BoolAlgTree.meetOp a b)
          (BoolAlgTree.complOp a) (BoolAlgTree.complOp b))
    have hstep : BooleanAlgebraTreeConv
        (BoolAlgTree.joinOp (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp a))
        (BoolAlgTree.joinOp b (BoolAlgTree.complOp a)) := by
      have c1 : BooleanAlgebraTreeConv
          (BoolAlgTree.joinOp (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp a))
          (BoolAlgTree.joinOp (BoolAlgTree.complOp a) (BoolAlgTree.meetOp a b)) :=
        BooleanAlgebraTreeConv.joinComm (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp a)
      have c2 : BooleanAlgebraTreeConv
          (BoolAlgTree.joinOp (BoolAlgTree.complOp a) (BoolAlgTree.meetOp a b))
          (BoolAlgTree.meetOp (BoolAlgTree.joinOp (BoolAlgTree.complOp a) a)
            (BoolAlgTree.joinOp (BoolAlgTree.complOp a) b)) :=
        BooleanAlgebraTreeConv.distribJoinMeet (BoolAlgTree.complOp a) a b
      have c3 : BooleanAlgebraTreeConv
          (BoolAlgTree.joinOp (BoolAlgTree.complOp a) a) BoolAlgTree.topOp :=
        (BooleanAlgebraTreeConv.joinComm (BoolAlgTree.complOp a) a).trans
          (BooleanAlgebraTreeConv.joinCompl a)
      have c4 : BooleanAlgebraTreeConv
          (BoolAlgTree.meetOp (BoolAlgTree.joinOp (BoolAlgTree.complOp a) a)
            (BoolAlgTree.joinOp (BoolAlgTree.complOp a) b))
          (BoolAlgTree.meetOp BoolAlgTree.topOp (BoolAlgTree.joinOp (BoolAlgTree.complOp a) b)) :=
        BooleanAlgebraTreeConv.meetCongr c3
          (BooleanAlgebraTreeConv.refl (BoolAlgTree.joinOp (BoolAlgTree.complOp a) b))
      have c5 : BooleanAlgebraTreeConv
          (BoolAlgTree.meetOp BoolAlgTree.topOp (BoolAlgTree.joinOp (BoolAlgTree.complOp a) b))
          (BoolAlgTree.joinOp (BoolAlgTree.complOp a) b) :=
        (BooleanAlgebraTreeConv.meetComm BoolAlgTree.topOp
            (BoolAlgTree.joinOp (BoolAlgTree.complOp a) b)).trans
          (BooleanAlgebraTreeConv.meetTop (BoolAlgTree.joinOp (BoolAlgTree.complOp a) b))
      have c6 : BooleanAlgebraTreeConv
          (BoolAlgTree.joinOp (BoolAlgTree.complOp a) b)
          (BoolAlgTree.joinOp b (BoolAlgTree.complOp a)) :=
        BooleanAlgebraTreeConv.joinComm (BoolAlgTree.complOp a) b
      exact c1.trans (c2.trans (c4.trans (c5.trans c6)))
    have hstep2 : BooleanAlgebraTreeConv
        (BoolAlgTree.joinOp (BoolAlgTree.joinOp (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp a))
          (BoolAlgTree.complOp b))
        (BoolAlgTree.joinOp (BoolAlgTree.joinOp b (BoolAlgTree.complOp a)) (BoolAlgTree.complOp b)) :=
      BooleanAlgebraTreeConv.joinCongr hstep (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp b))
    have hfin : BooleanAlgebraTreeConv
        (BoolAlgTree.joinOp (BoolAlgTree.joinOp b (BoolAlgTree.complOp a)) (BoolAlgTree.complOp b))
        BoolAlgTree.topOp := by
      have d1 : BooleanAlgebraTreeConv
          (BoolAlgTree.joinOp (BoolAlgTree.joinOp b (BoolAlgTree.complOp a)) (BoolAlgTree.complOp b))
          (BoolAlgTree.joinOp b
            (BoolAlgTree.joinOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b))) :=
        BooleanAlgebraTreeConv.joinAssoc b (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)
      have d2 : BooleanAlgebraTreeConv
          (BoolAlgTree.joinOp b (BoolAlgTree.joinOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)))
          (BoolAlgTree.joinOp b
            (BoolAlgTree.joinOp (BoolAlgTree.complOp b) (BoolAlgTree.complOp a))) :=
        BooleanAlgebraTreeConv.joinCongr (BooleanAlgebraTreeConv.refl b)
          (BooleanAlgebraTreeConv.joinComm (BoolAlgTree.complOp a) (BoolAlgTree.complOp b))
      have d3 : BooleanAlgebraTreeConv
          (BoolAlgTree.joinOp b (BoolAlgTree.joinOp (BoolAlgTree.complOp b) (BoolAlgTree.complOp a)))
          (BoolAlgTree.joinOp (BoolAlgTree.joinOp b (BoolAlgTree.complOp b)) (BoolAlgTree.complOp a)) :=
        BooleanAlgebraTreeConv.symm
          (BooleanAlgebraTreeConv.joinAssoc b (BoolAlgTree.complOp b) (BoolAlgTree.complOp a))
      have d4 : BooleanAlgebraTreeConv
          (BoolAlgTree.joinOp (BoolAlgTree.joinOp b (BoolAlgTree.complOp b)) (BoolAlgTree.complOp a))
          (BoolAlgTree.joinOp BoolAlgTree.topOp (BoolAlgTree.complOp a)) :=
        BooleanAlgebraTreeConv.joinCongr (BooleanAlgebraTreeConv.joinCompl b)
          (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp a))
      have d5 : BooleanAlgebraTreeConv
          (BoolAlgTree.joinOp BoolAlgTree.topOp (BoolAlgTree.complOp a)) BoolAlgTree.topOp :=
        (BooleanAlgebraTreeConv.joinComm BoolAlgTree.topOp (BoolAlgTree.complOp a)).trans
          (BooleanAlgebraTreeConv.joinTop (BoolAlgTree.complOp a))
      exact d1.trans (d2.trans (d3.trans (d4.trans d5)))
    exact hassoc.trans (hstep2.trans hfin)
  · have hd : BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp (BoolAlgTree.meetOp a b)
          (BoolAlgTree.joinOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)))
        (BoolAlgTree.joinOp
          (BoolAlgTree.meetOp (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp a))
          (BoolAlgTree.meetOp (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp b))) :=
      BooleanAlgebraTreeConv.distribMeetJoin (BoolAlgTree.meetOp a b)
        (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)
    have hL : BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp a)) BoolAlgTree.botOp := by
      have e1 : BooleanAlgebraTreeConv
          (BoolAlgTree.meetOp (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp a))
          (BoolAlgTree.meetOp (BoolAlgTree.meetOp b a) (BoolAlgTree.complOp a)) :=
        BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.meetComm a b)
          (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp a))
      have e2 : BooleanAlgebraTreeConv
          (BoolAlgTree.meetOp (BoolAlgTree.meetOp b a) (BoolAlgTree.complOp a))
          (BoolAlgTree.meetOp b (BoolAlgTree.meetOp a (BoolAlgTree.complOp a))) :=
        BooleanAlgebraTreeConv.meetAssoc b a (BoolAlgTree.complOp a)
      have e3 : BooleanAlgebraTreeConv
          (BoolAlgTree.meetOp b (BoolAlgTree.meetOp a (BoolAlgTree.complOp a)))
          (BoolAlgTree.meetOp b BoolAlgTree.botOp) :=
        BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl b)
          (BooleanAlgebraTreeConv.meetCompl a)
      have e4 : BooleanAlgebraTreeConv (BoolAlgTree.meetOp b BoolAlgTree.botOp) BoolAlgTree.botOp :=
        BooleanAlgebraTreeConv.meetBot b
      exact e1.trans (e2.trans (e3.trans e4))
    have hR : BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp b)) BoolAlgTree.botOp := by
      have e1 : BooleanAlgebraTreeConv
          (BoolAlgTree.meetOp (BoolAlgTree.meetOp a b) (BoolAlgTree.complOp b))
          (BoolAlgTree.meetOp a (BoolAlgTree.meetOp b (BoolAlgTree.complOp b))) :=
        BooleanAlgebraTreeConv.meetAssoc a b (BoolAlgTree.complOp b)
      have e2 : BooleanAlgebraTreeConv
          (BoolAlgTree.meetOp a (BoolAlgTree.meetOp b (BoolAlgTree.complOp b)))
          (BoolAlgTree.meetOp a BoolAlgTree.botOp) :=
        BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl a)
          (BooleanAlgebraTreeConv.meetCompl b)
      have e3 : BooleanAlgebraTreeConv (BoolAlgTree.meetOp a BoolAlgTree.botOp) BoolAlgTree.botOp :=
        BooleanAlgebraTreeConv.meetBot a
      exact e1.trans (e2.trans e3)
    exact hd.trans ((BooleanAlgebraTreeConv.joinCongr hL hR).trans
      (BooleanAlgebraTreeConv.joinIdem BoolAlgTree.botOp))

/-- ★ **De Morgan (join) at the convertibility level** `¬(a∨b) ≈ ¬a ∧ ¬b` — derived from the meet
version (applied to `¬a, ¬b`) plus double complement, avoiding a second long complement chain:
`¬(¬a∧¬b) ≈ ¬¬a ∨ ¬¬b ≈ a∨b`, complement both sides and cancel the outer double negation. -/
theorem booleanAlgebraDeMorganJoinConv (a b : BoolAlgTree) :
    BooleanAlgebraTreeConv (BoolAlgTree.complOp (BoolAlgTree.joinOp a b))
      (BoolAlgTree.meetOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)) := by
  have hm : BooleanAlgebraTreeConv
      (BoolAlgTree.complOp (BoolAlgTree.meetOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)))
      (BoolAlgTree.joinOp (BoolAlgTree.complOp (BoolAlgTree.complOp a))
        (BoolAlgTree.complOp (BoolAlgTree.complOp b))) :=
    booleanAlgebraDeMorganMeetConv (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)
  have h2 : BooleanAlgebraTreeConv
      (BoolAlgTree.joinOp (BoolAlgTree.complOp (BoolAlgTree.complOp a))
        (BoolAlgTree.complOp (BoolAlgTree.complOp b)))
      (BoolAlgTree.joinOp a b) :=
    BooleanAlgebraTreeConv.joinCongr (booleanAlgebraDoubleComplement a)
      (booleanAlgebraDoubleComplement b)
  have hcc : BooleanAlgebraTreeConv
      (BoolAlgTree.complOp
        (BoolAlgTree.complOp (BoolAlgTree.meetOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b))))
      (BoolAlgTree.complOp (BoolAlgTree.joinOp a b)) :=
    BooleanAlgebraTreeConv.complCongr (hm.trans h2)
  have h3 : BooleanAlgebraTreeConv
      (BoolAlgTree.complOp
        (BoolAlgTree.complOp (BoolAlgTree.meetOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b))))
      (BoolAlgTree.meetOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b)) :=
    booleanAlgebraDoubleComplement (BoolAlgTree.meetOp (BoolAlgTree.complOp a) (BoolAlgTree.complOp b))
  exact (BooleanAlgebraTreeConv.symm hcc).trans h3

/-! ## Small Bool / Nat helpers (structural, propext-clean) -/

/-- Structural Bool equality by full enumeration (no wildcard over the constructors). -/
def boolAlgBoolEq : Bool → Bool → Bool
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true

/-- `boolAlgBoolEq a a = true`. -/
theorem boolAlgBoolEq_refl (a : Bool) : boolAlgBoolEq a a = true := by cases a <;> rfl

/-- `boolAlgBoolEq a b = true → a = b`. -/
theorem boolAlgBoolEq_eq (a b : Bool) (h : boolAlgBoolEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact Bool.noConfusion h

/-- `(x && y) = true → x = true`. -/
theorem boolAlgAndTrueLeft (x y : Bool) (h : (x && y) = true) : x = true := by
  cases x with
  | true => rfl
  | false => exact Bool.noConfusion h

/-- `(x && y) = true → y = true`. -/
theorem boolAlgAndTrueRight (x y : Bool) (h : (x && y) = true) : y = true := by
  cases x with
  | true => exact h
  | false => exact Bool.noConfusion h

/-- `Nat.beq c c = true` — a purpose-built reflexivity, structural on the colour. -/
theorem boolAlgNatBeqRefl : ∀ (c : Nat), Nat.beq c c = true
  | 0 => rfl
  | Nat.succ n => boolAlgNatBeqRefl n

/-- `Nat.beq a b = true → a = b` — a purpose-built decision, structural (avoids any core lemma). -/
theorem boolAlgNatEqOfBeq : ∀ (a b : Nat), Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, Nat.succ _, h => Bool.noConfusion h
  | Nat.succ _, 0, h => Bool.noConfusion h
  | Nat.succ a, Nat.succ b, h => congrArg Nat.succ (boolAlgNatEqOfBeq a b h)

/-! ## Generator substitution (peel one generator to a constant) -/

/-- **Substitute `⊤` for `gen colour`** throughout a tree: on `gen d`, return `⊤` when `Nat.beq d colour`
holds and `gen d` otherwise; recurse structurally through the binary/unary nodes; fix `⊤`/`⊥`.  The
positive cofactor operator of the Shannon expansion. -/
def boolAlgSubstTop (colour : Nat) : BoolAlgTree → BoolAlgTree
  | .gen d => match Nat.beq d colour with
              | true => BoolAlgTree.topOp
              | false => BoolAlgTree.gen d
  | .topOp => BoolAlgTree.topOp
  | .botOp => BoolAlgTree.botOp
  | .meetOp l r => BoolAlgTree.meetOp (boolAlgSubstTop colour l) (boolAlgSubstTop colour r)
  | .joinOp l r => BoolAlgTree.joinOp (boolAlgSubstTop colour l) (boolAlgSubstTop colour r)
  | .complOp u => BoolAlgTree.complOp (boolAlgSubstTop colour u)

/-- **Substitute `⊥` for `gen colour`** throughout a tree — the negative cofactor operator. -/
def boolAlgSubstBot (colour : Nat) : BoolAlgTree → BoolAlgTree
  | .gen d => match Nat.beq d colour with
              | true => BoolAlgTree.botOp
              | false => BoolAlgTree.gen d
  | .topOp => BoolAlgTree.topOp
  | .botOp => BoolAlgTree.botOp
  | .meetOp l r => BoolAlgTree.meetOp (boolAlgSubstBot colour l) (boolAlgSubstBot colour r)
  | .joinOp l r => BoolAlgTree.joinOp (boolAlgSubstBot colour l) (boolAlgSubstBot colour r)
  | .complOp u => BoolAlgTree.complOp (boolAlgSubstBot colour u)

/-- Computation of `boolAlgSubstTop` at a matching generator. -/
theorem boolAlgSubstTop_gen_eq (colour d : Nat) (h : Nat.beq d colour = true) :
    boolAlgSubstTop colour (BoolAlgTree.gen d) = BoolAlgTree.topOp := by
  show (match Nat.beq d colour with | true => BoolAlgTree.topOp | false => BoolAlgTree.gen d)
    = BoolAlgTree.topOp
  rw [h]

/-- Computation of `boolAlgSubstTop` at a non-matching generator. -/
theorem boolAlgSubstTop_gen_ne (colour d : Nat) (h : Nat.beq d colour = false) :
    boolAlgSubstTop colour (BoolAlgTree.gen d) = BoolAlgTree.gen d := by
  show (match Nat.beq d colour with | true => BoolAlgTree.topOp | false => BoolAlgTree.gen d)
    = BoolAlgTree.gen d
  rw [h]

/-- Computation of `boolAlgSubstBot` at a matching generator. -/
theorem boolAlgSubstBot_gen_eq (colour d : Nat) (h : Nat.beq d colour = true) :
    boolAlgSubstBot colour (BoolAlgTree.gen d) = BoolAlgTree.botOp := by
  show (match Nat.beq d colour with | true => BoolAlgTree.botOp | false => BoolAlgTree.gen d)
    = BoolAlgTree.botOp
  rw [h]

/-- Computation of `boolAlgSubstBot` at a non-matching generator. -/
theorem boolAlgSubstBot_gen_ne (colour d : Nat) (h : Nat.beq d colour = false) :
    boolAlgSubstBot colour (BoolAlgTree.gen d) = BoolAlgTree.gen d := by
  show (match Nat.beq d colour with | true => BoolAlgTree.botOp | false => BoolAlgTree.gen d)
    = BoolAlgTree.gen d
  rw [h]

/-! ## Membership and support over a generator list -/

/-- Structural membership of a colour in a generator list, via `Nat.beq`. -/
def boolAlgListMem (colour : Nat) : List Nat → Bool
  | [] => false
  | g :: rest => Nat.beq colour g || boolAlgListMem colour rest

/-- **Support predicate** `boolAlgSupportedBy gens t` — every generator colour appearing in `t` is a
member of `gens`.  Structural fold: a `gen c` leaf is supported iff `c ∈ gens`; `⊤`/`⊥` always; the
binary/unary nodes conjoin their children. -/
def boolAlgSupportedBy (gens : List Nat) : BoolAlgTree → Bool
  | .gen c => boolAlgListMem c gens
  | .topOp => true
  | .botOp => true
  | .meetOp l r => boolAlgSupportedBy gens l && boolAlgSupportedBy gens r
  | .joinOp l r => boolAlgSupportedBy gens l && boolAlgSupportedBy gens r
  | .complOp u => boolAlgSupportedBy gens u

/-- Substituting `⊤` for `gens`' head generator shrinks the support to the tail. -/
theorem boolAlgSubstTop_supported (g : Nat) (rest : List Nat) :
    ∀ (t : BoolAlgTree), boolAlgSupportedBy (g :: rest) t = true →
      boolAlgSupportedBy rest (boolAlgSubstTop g t) = true := by
  intro t
  induction t with
  | gen d =>
      intro hsup
      cases hbg : Nat.beq d g with
      | true => rw [boolAlgSubstTop_gen_eq g d hbg]; rfl
      | false =>
          rw [boolAlgSubstTop_gen_ne g d hbg]
          show boolAlgListMem d rest = true
          have hmem : (Nat.beq d g || boolAlgListMem d rest) = true := hsup
          rw [hbg] at hmem
          exact hmem
  | topOp => intro _; rfl
  | botOp => intro _; rfl
  | meetOp l r ihl ihr =>
      intro hsup
      have hl := boolAlgAndTrueLeft _ _ hsup
      have hr := boolAlgAndTrueRight _ _ hsup
      show (boolAlgSupportedBy rest (boolAlgSubstTop g l)
        && boolAlgSupportedBy rest (boolAlgSubstTop g r)) = true
      rw [ihl hl, ihr hr]
      rfl
  | joinOp l r ihl ihr =>
      intro hsup
      have hl := boolAlgAndTrueLeft _ _ hsup
      have hr := boolAlgAndTrueRight _ _ hsup
      show (boolAlgSupportedBy rest (boolAlgSubstTop g l)
        && boolAlgSupportedBy rest (boolAlgSubstTop g r)) = true
      rw [ihl hl, ihr hr]
      rfl
  | complOp u ihu => intro hsup; exact ihu hsup

/-- Substituting `⊥` for `gens`' head generator shrinks the support to the tail. -/
theorem boolAlgSubstBot_supported (g : Nat) (rest : List Nat) :
    ∀ (t : BoolAlgTree), boolAlgSupportedBy (g :: rest) t = true →
      boolAlgSupportedBy rest (boolAlgSubstBot g t) = true := by
  intro t
  induction t with
  | gen d =>
      intro hsup
      cases hbg : Nat.beq d g with
      | true => rw [boolAlgSubstBot_gen_eq g d hbg]; rfl
      | false =>
          rw [boolAlgSubstBot_gen_ne g d hbg]
          show boolAlgListMem d rest = true
          have hmem : (Nat.beq d g || boolAlgListMem d rest) = true := hsup
          rw [hbg] at hmem
          exact hmem
  | topOp => intro _; rfl
  | botOp => intro _; rfl
  | meetOp l r ihl ihr =>
      intro hsup
      have hl := boolAlgAndTrueLeft _ _ hsup
      have hr := boolAlgAndTrueRight _ _ hsup
      show (boolAlgSupportedBy rest (boolAlgSubstBot g l)
        && boolAlgSupportedBy rest (boolAlgSubstBot g r)) = true
      rw [ihl hl, ihr hr]
      rfl
  | joinOp l r ihl ihr =>
      intro hsup
      have hl := boolAlgAndTrueLeft _ _ hsup
      have hr := boolAlgAndTrueRight _ _ hsup
      show (boolAlgSupportedBy rest (boolAlgSubstBot g l)
        && boolAlgSupportedBy rest (boolAlgSubstBot g r)) = true
      rw [ihl hl, ihr hr]
      rfl
  | complOp u ihu => intro hsup; exact ihu hsup

/-! ## Evaluation under substitution -/

/-- The constantly-`false` environment. -/
def boolAlgFalseEnv : Nat → Bool := fun _ => false

/-- The environment `env` overridden to send `colour` to `true`. -/
def boolAlgEnvSetTop (colour : Nat) (env : Nat → Bool) : Nat → Bool :=
  fun x => match Nat.beq x colour with
           | true => true
           | false => env x

/-- The environment `env` overridden to send `colour` to `false`. -/
def boolAlgEnvSetBot (colour : Nat) (env : Nat → Bool) : Nat → Bool :=
  fun x => match Nat.beq x colour with
           | true => false
           | false => env x

/-- Evaluating a `⊤`-substituted tree equals evaluating the original under the `true`-overridden env. -/
theorem boolAlgEval_substTop : ∀ (env : Nat → Bool) (colour : Nat) (t : BoolAlgTree),
    evalBoolAlgTree env (boolAlgSubstTop colour t)
      = evalBoolAlgTree (boolAlgEnvSetTop colour env) t := by
  intro env colour t
  induction t with
  | gen d =>
      cases hbd : Nat.beq d colour with
      | true =>
          rw [boolAlgSubstTop_gen_eq colour d hbd]
          show (true : Bool) = boolAlgEnvSetTop colour env d
          show (true : Bool) = (match Nat.beq d colour with | true => true | false => env d)
          rw [hbd]
      | false =>
          rw [boolAlgSubstTop_gen_ne colour d hbd]
          show env d = boolAlgEnvSetTop colour env d
          show env d = (match Nat.beq d colour with | true => true | false => env d)
          rw [hbd]
  | topOp => rfl
  | botOp => rfl
  | meetOp l r ihl ihr =>
      show (evalBoolAlgTree env (boolAlgSubstTop colour l)
        && evalBoolAlgTree env (boolAlgSubstTop colour r))
        = (evalBoolAlgTree (boolAlgEnvSetTop colour env) l
          && evalBoolAlgTree (boolAlgEnvSetTop colour env) r)
      rw [ihl, ihr]
  | joinOp l r ihl ihr =>
      show (evalBoolAlgTree env (boolAlgSubstTop colour l)
        || evalBoolAlgTree env (boolAlgSubstTop colour r))
        = (evalBoolAlgTree (boolAlgEnvSetTop colour env) l
          || evalBoolAlgTree (boolAlgEnvSetTop colour env) r)
      rw [ihl, ihr]
  | complOp u ihu =>
      show (! evalBoolAlgTree env (boolAlgSubstTop colour u))
        = (! evalBoolAlgTree (boolAlgEnvSetTop colour env) u)
      rw [ihu]

/-- Evaluating a `⊥`-substituted tree equals evaluating the original under the `false`-overridden env. -/
theorem boolAlgEval_substBot : ∀ (env : Nat → Bool) (colour : Nat) (t : BoolAlgTree),
    evalBoolAlgTree env (boolAlgSubstBot colour t)
      = evalBoolAlgTree (boolAlgEnvSetBot colour env) t := by
  intro env colour t
  induction t with
  | gen d =>
      cases hbd : Nat.beq d colour with
      | true =>
          rw [boolAlgSubstBot_gen_eq colour d hbd]
          show (false : Bool) = boolAlgEnvSetBot colour env d
          show (false : Bool) = (match Nat.beq d colour with | true => false | false => env d)
          rw [hbd]
      | false =>
          rw [boolAlgSubstBot_gen_ne colour d hbd]
          show env d = boolAlgEnvSetBot colour env d
          show env d = (match Nat.beq d colour with | true => false | false => env d)
          rw [hbd]
  | topOp => rfl
  | botOp => rfl
  | meetOp l r ihl ihr =>
      show (evalBoolAlgTree env (boolAlgSubstBot colour l)
        && evalBoolAlgTree env (boolAlgSubstBot colour r))
        = (evalBoolAlgTree (boolAlgEnvSetBot colour env) l
          && evalBoolAlgTree (boolAlgEnvSetBot colour env) r)
      rw [ihl, ihr]
  | joinOp l r ihl ihr =>
      show (evalBoolAlgTree env (boolAlgSubstBot colour l)
        || evalBoolAlgTree env (boolAlgSubstBot colour r))
        = (evalBoolAlgTree (boolAlgEnvSetBot colour env) l
          || evalBoolAlgTree (boolAlgEnvSetBot colour env) r)
      rw [ihl, ihr]
  | complOp u ihu =>
      show (! evalBoolAlgTree env (boolAlgSubstBot colour u))
        = (! evalBoolAlgTree (boolAlgEnvSetBot colour env) u)
      rw [ihu]

/-! ## The generator-restriction pairs (the crux double induction) -/

/-- ★ **Generator restriction under a positive context (paired double induction).**  Meeting with
`gen c`, replacing `gen c` by `⊤` throughout is invisible — AND the same holds for the complemented
subtree.  Both halves are proved SIMULTANEOUSLY so the complement case of each half can consume the
OTHER half of the induction hypothesis (complement is not monotone under a fixed meet, so it must be
carried alongside).  The complement subcases of the binary nodes are where the Conv-level De Morgan
laws (`booleanAlgebraDeMorganMeetConv` / `booleanAlgebraDeMorganJoinConv`) enter. -/
theorem boolAlgGenRestrictTopPair (c : Nat) : ∀ (t : BoolAlgTree),
    BooleanAlgebraTreeConv (BoolAlgTree.meetOp (BoolAlgTree.gen c) t)
        (BoolAlgTree.meetOp (BoolAlgTree.gen c) (boolAlgSubstTop c t))
      ∧ BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp t))
        (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp (boolAlgSubstTop c t))) := by
  intro t
  induction t with
  | gen d =>
      cases hbd : Nat.beq d c with
      | true =>
          have hdc : d = c := boolAlgNatEqOfBeq d c hbd
          subst hdc
          rw [boolAlgSubstTop_gen_eq d d (boolAlgNatBeqRefl d)]
          refine ⟨?_, ?_⟩
          · exact (BooleanAlgebraTreeConv.meetIdem (BoolAlgTree.gen d)).trans
              (BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.meetTop (BoolAlgTree.gen d)))
          · have hB : BooleanAlgebraTreeConv
                (BoolAlgTree.meetOp (BoolAlgTree.gen d) (BoolAlgTree.complOp BoolAlgTree.topOp))
                BoolAlgTree.botOp :=
              (BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl (BoolAlgTree.gen d))
                boolAlgComplTop).trans (BooleanAlgebraTreeConv.meetBot (BoolAlgTree.gen d))
            exact (BooleanAlgebraTreeConv.meetCompl (BoolAlgTree.gen d)).trans
              (BooleanAlgebraTreeConv.symm hB)
      | false =>
          rw [boolAlgSubstTop_gen_ne c d hbd]
          exact ⟨BooleanAlgebraTreeConv.refl _, BooleanAlgebraTreeConv.refl _⟩
  | topOp => exact ⟨BooleanAlgebraTreeConv.refl _, BooleanAlgebraTreeConv.refl _⟩
  | botOp => exact ⟨BooleanAlgebraTreeConv.refl _, BooleanAlgebraTreeConv.refl _⟩
  | meetOp l r ihl ihr =>
      refine ⟨?_, ?_⟩
      · have s1 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.meetOp l r))
            (BoolAlgTree.meetOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.gen c))
              (BoolAlgTree.meetOp l r)) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.meetIdem (BoolAlgTree.gen c)))
            (BooleanAlgebraTreeConv.refl (BoolAlgTree.meetOp l r))
        have s2 := boolAlgMeetMiddleSwap (BoolAlgTree.gen c) (BoolAlgTree.gen c) l r
        have s3 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) l)
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) r))
            (BoolAlgTree.meetOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) (boolAlgSubstTop c l))
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (boolAlgSubstTop c r))) :=
          BooleanAlgebraTreeConv.meetCongr ihl.1 ihr.1
        have s4 := BooleanAlgebraTreeConv.symm
          (boolAlgMeetMiddleSwap (BoolAlgTree.gen c) (BoolAlgTree.gen c)
            (boolAlgSubstTop c l) (boolAlgSubstTop c r))
        have s5 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.gen c))
              (BoolAlgTree.meetOp (boolAlgSubstTop c l) (boolAlgSubstTop c r)))
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.meetOp (boolAlgSubstTop c l) (boolAlgSubstTop c r))) :=
          BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.meetIdem (BoolAlgTree.gen c))
            (BooleanAlgebraTreeConv.refl
              (BoolAlgTree.meetOp (boolAlgSubstTop c l) (boolAlgSubstTop c r)))
        exact s1.trans (s2.trans (s3.trans (s4.trans s5)))
      · have s1 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp (BoolAlgTree.meetOp l r)))
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.joinOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r))) :=
          BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl (BoolAlgTree.gen c))
            (booleanAlgebraDeMorganMeetConv l r)
        have s2 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.joinOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r)))
            (BoolAlgTree.joinOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp l))
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp r))) :=
          BooleanAlgebraTreeConv.distribMeetJoin (BoolAlgTree.gen c)
            (BoolAlgTree.complOp l) (BoolAlgTree.complOp r)
        have s3 : BooleanAlgebraTreeConv
            (BoolAlgTree.joinOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp l))
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp r)))
            (BoolAlgTree.joinOp
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp (boolAlgSubstTop c l)))
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp (boolAlgSubstTop c r)))) :=
          BooleanAlgebraTreeConv.joinCongr ihl.2 ihr.2
        have s4 : BooleanAlgebraTreeConv
            (BoolAlgTree.joinOp
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp (boolAlgSubstTop c l)))
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp (boolAlgSubstTop c r))))
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.joinOp (BoolAlgTree.complOp (boolAlgSubstTop c l))
                (BoolAlgTree.complOp (boolAlgSubstTop c r)))) :=
          BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.distribMeetJoin (BoolAlgTree.gen c)
            (BoolAlgTree.complOp (boolAlgSubstTop c l)) (BoolAlgTree.complOp (boolAlgSubstTop c r)))
        have s5 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.joinOp (BoolAlgTree.complOp (boolAlgSubstTop c l))
                (BoolAlgTree.complOp (boolAlgSubstTop c r))))
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.complOp
                (BoolAlgTree.meetOp (boolAlgSubstTop c l) (boolAlgSubstTop c r)))) :=
          BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl (BoolAlgTree.gen c))
            (BooleanAlgebraTreeConv.symm
              (booleanAlgebraDeMorganMeetConv (boolAlgSubstTop c l) (boolAlgSubstTop c r)))
        exact s1.trans (s2.trans (s3.trans (s4.trans s5)))
  | joinOp l r ihl ihr =>
      refine ⟨?_, ?_⟩
      · have s1 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.joinOp l r))
            (BoolAlgTree.joinOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) l)
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) r)) :=
          BooleanAlgebraTreeConv.distribMeetJoin (BoolAlgTree.gen c) l r
        have s2 : BooleanAlgebraTreeConv
            (BoolAlgTree.joinOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) l)
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) r))
            (BoolAlgTree.joinOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) (boolAlgSubstTop c l))
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (boolAlgSubstTop c r))) :=
          BooleanAlgebraTreeConv.joinCongr ihl.1 ihr.1
        have s3 : BooleanAlgebraTreeConv
            (BoolAlgTree.joinOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) (boolAlgSubstTop c l))
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (boolAlgSubstTop c r)))
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.joinOp (boolAlgSubstTop c l) (boolAlgSubstTop c r))) :=
          BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.distribMeetJoin (BoolAlgTree.gen c)
            (boolAlgSubstTop c l) (boolAlgSubstTop c r))
        exact s1.trans (s2.trans s3)
      · have s1 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp (BoolAlgTree.joinOp l r)))
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.meetOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r))) :=
          BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl (BoolAlgTree.gen c))
            (booleanAlgebraDeMorganJoinConv l r)
        have s2 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.meetOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r)))
            (BoolAlgTree.meetOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.gen c))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r))) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.symm (BooleanAlgebraTreeConv.meetIdem (BoolAlgTree.gen c)))
            (BooleanAlgebraTreeConv.refl
              (BoolAlgTree.meetOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r)))
        have s3 := boolAlgMeetMiddleSwap (BoolAlgTree.gen c) (BoolAlgTree.gen c)
          (BoolAlgTree.complOp l) (BoolAlgTree.complOp r)
        have s4 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp l))
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp r)))
            (BoolAlgTree.meetOp
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp (boolAlgSubstTop c l)))
              (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp (boolAlgSubstTop c r)))) :=
          BooleanAlgebraTreeConv.meetCongr ihl.2 ihr.2
        have s5 := BooleanAlgebraTreeConv.symm
          (boolAlgMeetMiddleSwap (BoolAlgTree.gen c) (BoolAlgTree.gen c)
            (BoolAlgTree.complOp (boolAlgSubstTop c l)) (BoolAlgTree.complOp (boolAlgSubstTop c r)))
        have s6 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.gen c))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (boolAlgSubstTop c l))
                (BoolAlgTree.complOp (boolAlgSubstTop c r))))
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (boolAlgSubstTop c l))
                (BoolAlgTree.complOp (boolAlgSubstTop c r)))) :=
          BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.meetIdem (BoolAlgTree.gen c))
            (BooleanAlgebraTreeConv.refl
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (boolAlgSubstTop c l))
                (BoolAlgTree.complOp (boolAlgSubstTop c r))))
        have s7 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (boolAlgSubstTop c l))
                (BoolAlgTree.complOp (boolAlgSubstTop c r))))
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.complOp
                (BoolAlgTree.joinOp (boolAlgSubstTop c l) (boolAlgSubstTop c r)))) :=
          BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl (BoolAlgTree.gen c))
            (BooleanAlgebraTreeConv.symm
              (booleanAlgebraDeMorganJoinConv (boolAlgSubstTop c l) (boolAlgSubstTop c r)))
        exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))
  | complOp u ihu =>
      refine ⟨?_, ?_⟩
      · exact ihu.2
      · have dcU := booleanAlgebraDoubleComplement u
        have dcS := booleanAlgebraDoubleComplement (boolAlgSubstTop c u)
        have s1 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.gen c) (BoolAlgTree.complOp (BoolAlgTree.complOp u)))
            (BoolAlgTree.meetOp (BoolAlgTree.gen c) u) :=
          BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl (BoolAlgTree.gen c)) dcU
        have s3 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.gen c) (boolAlgSubstTop c u))
            (BoolAlgTree.meetOp (BoolAlgTree.gen c)
              (BoolAlgTree.complOp (BoolAlgTree.complOp (boolAlgSubstTop c u)))) :=
          BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl (BoolAlgTree.gen c))
            (BooleanAlgebraTreeConv.symm dcS)
        exact s1.trans (ihu.1.trans s3)

/-- ★ **Generator restriction under a negative context** — the De Morgan dual of the positive pair:
meeting with `¬gen c`, replacing `gen c` by `⊥` is invisible, complemented subtree included. -/
theorem boolAlgGenRestrictBotPair (c : Nat) : ∀ (t : BoolAlgTree),
    BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) t)
        (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (boolAlgSubstBot c t))
      ∧ BooleanAlgebraTreeConv
        (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (BoolAlgTree.complOp t))
        (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
          (BoolAlgTree.complOp (boolAlgSubstBot c t))) := by
  intro t
  induction t with
  | gen d =>
      cases hbd : Nat.beq d c with
      | true =>
          have hdc : d = c := boolAlgNatEqOfBeq d c hbd
          subst hdc
          rw [boolAlgSubstBot_gen_eq d d (boolAlgNatBeqRefl d)]
          refine ⟨?_, ?_⟩
          · have hA : BooleanAlgebraTreeConv
                (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen d)) (BoolAlgTree.gen d))
                BoolAlgTree.botOp :=
              (BooleanAlgebraTreeConv.meetComm (BoolAlgTree.complOp (BoolAlgTree.gen d))
                (BoolAlgTree.gen d)).trans (BooleanAlgebraTreeConv.meetCompl (BoolAlgTree.gen d))
            exact hA.trans (BooleanAlgebraTreeConv.symm
              (BooleanAlgebraTreeConv.meetBot (BoolAlgTree.complOp (BoolAlgTree.gen d))))
          · have hB : BooleanAlgebraTreeConv
                (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen d))
                  (BoolAlgTree.complOp BoolAlgTree.botOp))
                (BoolAlgTree.complOp (BoolAlgTree.gen d)) :=
              (BooleanAlgebraTreeConv.meetCongr
                (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp (BoolAlgTree.gen d)))
                boolAlgComplBot).trans
                (BooleanAlgebraTreeConv.meetTop (BoolAlgTree.complOp (BoolAlgTree.gen d)))
            exact (BooleanAlgebraTreeConv.meetIdem (BoolAlgTree.complOp (BoolAlgTree.gen d))).trans
              (BooleanAlgebraTreeConv.symm hB)
      | false =>
          rw [boolAlgSubstBot_gen_ne c d hbd]
          exact ⟨BooleanAlgebraTreeConv.refl _, BooleanAlgebraTreeConv.refl _⟩
  | topOp => exact ⟨BooleanAlgebraTreeConv.refl _, BooleanAlgebraTreeConv.refl _⟩
  | botOp => exact ⟨BooleanAlgebraTreeConv.refl _, BooleanAlgebraTreeConv.refl _⟩
  | meetOp l r ihl ihr =>
      refine ⟨?_, ?_⟩
      · have s1 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (BoolAlgTree.meetOp l r))
            (BoolAlgTree.meetOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
                (BoolAlgTree.complOp (BoolAlgTree.gen c)))
              (BoolAlgTree.meetOp l r)) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.symm
              (BooleanAlgebraTreeConv.meetIdem (BoolAlgTree.complOp (BoolAlgTree.gen c))))
            (BooleanAlgebraTreeConv.refl (BoolAlgTree.meetOp l r))
        have s2 := boolAlgMeetMiddleSwap (BoolAlgTree.complOp (BoolAlgTree.gen c))
          (BoolAlgTree.complOp (BoolAlgTree.gen c)) l r
        have s3 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) l)
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) r))
            (BoolAlgTree.meetOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (boolAlgSubstBot c l))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (boolAlgSubstBot c r))) :=
          BooleanAlgebraTreeConv.meetCongr ihl.1 ihr.1
        have s4 := BooleanAlgebraTreeConv.symm
          (boolAlgMeetMiddleSwap (BoolAlgTree.complOp (BoolAlgTree.gen c))
            (BoolAlgTree.complOp (BoolAlgTree.gen c))
            (boolAlgSubstBot c l) (boolAlgSubstBot c r))
        have s5 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
                (BoolAlgTree.complOp (BoolAlgTree.gen c)))
              (BoolAlgTree.meetOp (boolAlgSubstBot c l) (boolAlgSubstBot c r)))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.meetOp (boolAlgSubstBot c l) (boolAlgSubstBot c r))) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.meetIdem (BoolAlgTree.complOp (BoolAlgTree.gen c)))
            (BooleanAlgebraTreeConv.refl
              (BoolAlgTree.meetOp (boolAlgSubstBot c l) (boolAlgSubstBot c r)))
        exact s1.trans (s2.trans (s3.trans (s4.trans s5)))
      · have s1 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.complOp (BoolAlgTree.meetOp l r)))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.joinOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r))) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp (BoolAlgTree.gen c)))
            (booleanAlgebraDeMorganMeetConv l r)
        have s2 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.joinOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r)))
            (BoolAlgTree.joinOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (BoolAlgTree.complOp l))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (BoolAlgTree.complOp r))) :=
          BooleanAlgebraTreeConv.distribMeetJoin (BoolAlgTree.complOp (BoolAlgTree.gen c))
            (BoolAlgTree.complOp l) (BoolAlgTree.complOp r)
        have s3 : BooleanAlgebraTreeConv
            (BoolAlgTree.joinOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (BoolAlgTree.complOp l))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (BoolAlgTree.complOp r)))
            (BoolAlgTree.joinOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
                (BoolAlgTree.complOp (boolAlgSubstBot c l)))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
                (BoolAlgTree.complOp (boolAlgSubstBot c r)))) :=
          BooleanAlgebraTreeConv.joinCongr ihl.2 ihr.2
        have s4 : BooleanAlgebraTreeConv
            (BoolAlgTree.joinOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
                (BoolAlgTree.complOp (boolAlgSubstBot c l)))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
                (BoolAlgTree.complOp (boolAlgSubstBot c r))))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.joinOp (BoolAlgTree.complOp (boolAlgSubstBot c l))
                (BoolAlgTree.complOp (boolAlgSubstBot c r)))) :=
          BooleanAlgebraTreeConv.symm
            (BooleanAlgebraTreeConv.distribMeetJoin (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.complOp (boolAlgSubstBot c l)) (BoolAlgTree.complOp (boolAlgSubstBot c r)))
        have s5 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.joinOp (BoolAlgTree.complOp (boolAlgSubstBot c l))
                (BoolAlgTree.complOp (boolAlgSubstBot c r))))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.complOp
                (BoolAlgTree.meetOp (boolAlgSubstBot c l) (boolAlgSubstBot c r)))) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp (BoolAlgTree.gen c)))
            (BooleanAlgebraTreeConv.symm
              (booleanAlgebraDeMorganMeetConv (boolAlgSubstBot c l) (boolAlgSubstBot c r)))
        exact s1.trans (s2.trans (s3.trans (s4.trans s5)))
  | joinOp l r ihl ihr =>
      refine ⟨?_, ?_⟩
      · have s1 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (BoolAlgTree.joinOp l r))
            (BoolAlgTree.joinOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) l)
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) r)) :=
          BooleanAlgebraTreeConv.distribMeetJoin (BoolAlgTree.complOp (BoolAlgTree.gen c)) l r
        have s2 : BooleanAlgebraTreeConv
            (BoolAlgTree.joinOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) l)
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) r))
            (BoolAlgTree.joinOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (boolAlgSubstBot c l))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (boolAlgSubstBot c r))) :=
          BooleanAlgebraTreeConv.joinCongr ihl.1 ihr.1
        have s3 : BooleanAlgebraTreeConv
            (BoolAlgTree.joinOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (boolAlgSubstBot c l))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (boolAlgSubstBot c r)))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.joinOp (boolAlgSubstBot c l) (boolAlgSubstBot c r))) :=
          BooleanAlgebraTreeConv.symm
            (BooleanAlgebraTreeConv.distribMeetJoin (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (boolAlgSubstBot c l) (boolAlgSubstBot c r))
        exact s1.trans (s2.trans s3)
      · have s1 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.complOp (BoolAlgTree.joinOp l r)))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r))) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp (BoolAlgTree.gen c)))
            (booleanAlgebraDeMorganJoinConv l r)
        have s2 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r)))
            (BoolAlgTree.meetOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
                (BoolAlgTree.complOp (BoolAlgTree.gen c)))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r))) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.symm
              (BooleanAlgebraTreeConv.meetIdem (BoolAlgTree.complOp (BoolAlgTree.gen c))))
            (BooleanAlgebraTreeConv.refl
              (BoolAlgTree.meetOp (BoolAlgTree.complOp l) (BoolAlgTree.complOp r)))
        have s3 := boolAlgMeetMiddleSwap (BoolAlgTree.complOp (BoolAlgTree.gen c))
          (BoolAlgTree.complOp (BoolAlgTree.gen c)) (BoolAlgTree.complOp l) (BoolAlgTree.complOp r)
        have s4 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (BoolAlgTree.complOp l))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (BoolAlgTree.complOp r)))
            (BoolAlgTree.meetOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
                (BoolAlgTree.complOp (boolAlgSubstBot c l)))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
                (BoolAlgTree.complOp (boolAlgSubstBot c r)))) :=
          BooleanAlgebraTreeConv.meetCongr ihl.2 ihr.2
        have s5 := BooleanAlgebraTreeConv.symm
          (boolAlgMeetMiddleSwap (BoolAlgTree.complOp (BoolAlgTree.gen c))
            (BoolAlgTree.complOp (BoolAlgTree.gen c))
            (BoolAlgTree.complOp (boolAlgSubstBot c l)) (BoolAlgTree.complOp (boolAlgSubstBot c r)))
        have s6 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
                (BoolAlgTree.complOp (BoolAlgTree.gen c)))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (boolAlgSubstBot c l))
                (BoolAlgTree.complOp (boolAlgSubstBot c r))))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (boolAlgSubstBot c l))
                (BoolAlgTree.complOp (boolAlgSubstBot c r)))) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.meetIdem (BoolAlgTree.complOp (BoolAlgTree.gen c)))
            (BooleanAlgebraTreeConv.refl
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (boolAlgSubstBot c l))
                (BoolAlgTree.complOp (boolAlgSubstBot c r))))
        have s7 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.meetOp (BoolAlgTree.complOp (boolAlgSubstBot c l))
                (BoolAlgTree.complOp (boolAlgSubstBot c r))))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.complOp
                (BoolAlgTree.joinOp (boolAlgSubstBot c l) (boolAlgSubstBot c r)))) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp (BoolAlgTree.gen c)))
            (BooleanAlgebraTreeConv.symm
              (booleanAlgebraDeMorganJoinConv (boolAlgSubstBot c l) (boolAlgSubstBot c r)))
        exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))
  | complOp u ihu =>
      refine ⟨?_, ?_⟩
      · exact ihu.2
      · have dcU := booleanAlgebraDoubleComplement u
        have dcS := booleanAlgebraDoubleComplement (boolAlgSubstBot c u)
        have s1 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.complOp (BoolAlgTree.complOp u)))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) u) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp (BoolAlgTree.gen c))) dcU
        have s3 : BooleanAlgebraTreeConv
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (boolAlgSubstBot c u))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c))
              (BoolAlgTree.complOp (BoolAlgTree.complOp (boolAlgSubstBot c u)))) :=
          BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp (BoolAlgTree.gen c)))
            (BooleanAlgebraTreeConv.symm dcS)
        exact s1.trans (ihu.1.trans s3)

/-- ★ **The full Shannon cofactor decomposition** `t ≈ (gen c ∧ t[c:=⊤]) ∨ (¬gen c ∧ t[c:=⊥])` — a
GENUINE `BooleanAlgebraTreeConv` derivation.  Combines the cofactor split (which peels `gen c`) with
the two restriction lemmas (which replace `gen c` by the constant its context forces).  Iterating this
over a generator list drives the truth-table decision. -/
theorem boolAlgFullShannon (c : Nat) (t : BoolAlgTree) :
    BooleanAlgebraTreeConv t
      (BoolAlgTree.joinOp
        (BoolAlgTree.meetOp (BoolAlgTree.gen c) (boolAlgSubstTop c t))
        (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen c)) (boolAlgSubstBot c t))) :=
  (booleanAlgebraCofactorSplit c t).trans
    (BooleanAlgebraTreeConv.joinCongr (boolAlgGenRestrictTopPair c t).1
      (boolAlgGenRestrictBotPair c t).1)

/-! ## The closed base: a generator-free tree reduces to a constant -/

/-- The Boolean-algebra constant realizing a truth value: `true ↦ ⊤`, `false ↦ ⊥`. -/
def boolAlgConstOfBool : Bool → BoolAlgTree
  | true => BoolAlgTree.topOp
  | false => BoolAlgTree.botOp

/-- Meet of two constants folds to the constant of their conjunction. -/
theorem boolAlgMeetConst (a b : Bool) :
    BooleanAlgebraTreeConv (BoolAlgTree.meetOp (boolAlgConstOfBool a) (boolAlgConstOfBool b))
      (boolAlgConstOfBool (a && b)) := by
  cases a with
  | true =>
      cases b with
      | true => exact BooleanAlgebraTreeConv.meetTop BoolAlgTree.topOp
      | false => exact BooleanAlgebraTreeConv.meetBot BoolAlgTree.topOp
  | false =>
      cases b with
      | true => exact BooleanAlgebraTreeConv.meetTop BoolAlgTree.botOp
      | false => exact BooleanAlgebraTreeConv.meetBot BoolAlgTree.botOp

/-- Join of two constants folds to the constant of their disjunction. -/
theorem boolAlgJoinConst (a b : Bool) :
    BooleanAlgebraTreeConv (BoolAlgTree.joinOp (boolAlgConstOfBool a) (boolAlgConstOfBool b))
      (boolAlgConstOfBool (a || b)) := by
  cases a with
  | true =>
      cases b with
      | true => exact BooleanAlgebraTreeConv.joinTop BoolAlgTree.topOp
      | false => exact BooleanAlgebraTreeConv.joinBot BoolAlgTree.topOp
  | false =>
      cases b with
      | true => exact BooleanAlgebraTreeConv.joinTop BoolAlgTree.botOp
      | false => exact BooleanAlgebraTreeConv.joinBot BoolAlgTree.botOp

/-- Complement of a constant folds to the constant of its negation. -/
theorem boolAlgComplConst (a : Bool) :
    BooleanAlgebraTreeConv (BoolAlgTree.complOp (boolAlgConstOfBool a)) (boolAlgConstOfBool (! a)) := by
  cases a with
  | true => exact boolAlgComplTop
  | false => exact boolAlgComplBot

/-- ★ **A generator-free tree is convertible to a constant** — the base case of the truth-table
decision.  A tree supported by the EMPTY generator list has no generators, so its evaluation is
environment-independent; structural induction folds each node's children (already constants by IH)
through `boolAlgMeetConst` / `boolAlgJoinConst` / `boolAlgComplConst`. -/
theorem boolAlgClosedToConst : ∀ (t : BoolAlgTree), boolAlgSupportedBy [] t = true →
    BooleanAlgebraTreeConv t (boolAlgConstOfBool (evalBoolAlgTree boolAlgFalseEnv t)) := by
  intro t
  induction t with
  | gen c => intro hsup; exact Bool.noConfusion hsup
  | topOp => intro _; exact BooleanAlgebraTreeConv.refl BoolAlgTree.topOp
  | botOp => intro _; exact BooleanAlgebraTreeConv.refl BoolAlgTree.botOp
  | meetOp l r ihl ihr =>
      intro hsup
      have hl := boolAlgAndTrueLeft _ _ hsup
      have hr := boolAlgAndTrueRight _ _ hsup
      exact (BooleanAlgebraTreeConv.meetCongr (ihl hl) (ihr hr)).trans
        (boolAlgMeetConst (evalBoolAlgTree boolAlgFalseEnv l) (evalBoolAlgTree boolAlgFalseEnv r))
  | joinOp l r ihl ihr =>
      intro hsup
      have hl := boolAlgAndTrueLeft _ _ hsup
      have hr := boolAlgAndTrueRight _ _ hsup
      exact (BooleanAlgebraTreeConv.joinCongr (ihl hl) (ihr hr)).trans
        (boolAlgJoinConst (evalBoolAlgTree boolAlgFalseEnv l) (evalBoolAlgTree boolAlgFalseEnv r))
  | complOp u ihu =>
      intro hsup
      exact (BooleanAlgebraTreeConv.complCongr (ihu hsup)).trans
        (boolAlgComplConst (evalBoolAlgTree boolAlgFalseEnv u))

/-! ## Generator-list concatenation and colour collection -/

/-- Cons-only concatenation of generator lists (a purpose-built append; no `List.append`/`++`). -/
def boolAlgCat : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: boolAlgCat xs ys

/-- Membership through a concatenation is the disjunction of memberships. -/
theorem boolAlgListMem_cat (colour : Nat) : ∀ (xs ys : List Nat),
    boolAlgListMem colour (boolAlgCat xs ys)
      = (boolAlgListMem colour xs || boolAlgListMem colour ys) := by
  intro xs
  induction xs with
  | nil => intro ys; rfl
  | cons x xs ih =>
      intro ys
      show (Nat.beq colour x || boolAlgListMem colour (boolAlgCat xs ys))
        = ((Nat.beq colour x || boolAlgListMem colour xs) || boolAlgListMem colour ys)
      rw [ih ys]
      cases Nat.beq colour x <;> cases boolAlgListMem colour xs <;>
        cases boolAlgListMem colour ys <;> rfl

/-- The colours (generators) appearing in a tree, cons-collected (possibly with repeats). -/
def boolAlgColours : BoolAlgTree → List Nat
  | .gen c => [c]
  | .topOp => []
  | .botOp => []
  | .meetOp l r => boolAlgCat (boolAlgColours l) (boolAlgColours r)
  | .joinOp l r => boolAlgCat (boolAlgColours l) (boolAlgColours r)
  | .complOp u => boolAlgColours u

/-- Support is monotone in the generator list. -/
theorem boolAlgSupported_weaken (gens gens' : List Nat)
    (hmono : ∀ c, boolAlgListMem c gens = true → boolAlgListMem c gens' = true) :
    ∀ (t : BoolAlgTree), boolAlgSupportedBy gens t = true → boolAlgSupportedBy gens' t = true := by
  intro t
  induction t with
  | gen c => intro hsup; exact hmono c hsup
  | topOp => intro _; rfl
  | botOp => intro _; rfl
  | meetOp l r ihl ihr =>
      intro hsup
      have hl := boolAlgAndTrueLeft _ _ hsup
      have hr := boolAlgAndTrueRight _ _ hsup
      show (boolAlgSupportedBy gens' l && boolAlgSupportedBy gens' r) = true
      rw [ihl hl, ihr hr]
      rfl
  | joinOp l r ihl ihr =>
      intro hsup
      have hl := boolAlgAndTrueLeft _ _ hsup
      have hr := boolAlgAndTrueRight _ _ hsup
      show (boolAlgSupportedBy gens' l && boolAlgSupportedBy gens' r) = true
      rw [ihl hl, ihr hr]
      rfl
  | complOp u ihu => intro hsup; exact ihu hsup

/-- A tree is supported by its own collected colour list. -/
theorem boolAlgSelfSupported : ∀ (t : BoolAlgTree),
    boolAlgSupportedBy (boolAlgColours t) t = true := by
  intro t
  induction t with
  | gen c =>
      show (Nat.beq c c || false) = true
      rw [boolAlgNatBeqRefl c]
      rfl
  | topOp => rfl
  | botOp => rfl
  | meetOp l r ihl ihr =>
      show (boolAlgSupportedBy (boolAlgCat (boolAlgColours l) (boolAlgColours r)) l
        && boolAlgSupportedBy (boolAlgCat (boolAlgColours l) (boolAlgColours r)) r) = true
      have hl : boolAlgSupportedBy (boolAlgCat (boolAlgColours l) (boolAlgColours r)) l = true :=
        boolAlgSupported_weaken (boolAlgColours l)
          (boolAlgCat (boolAlgColours l) (boolAlgColours r))
          (fun c hc => by rw [boolAlgListMem_cat, hc]; rfl) l ihl
      have hr : boolAlgSupportedBy (boolAlgCat (boolAlgColours l) (boolAlgColours r)) r = true :=
        boolAlgSupported_weaken (boolAlgColours r)
          (boolAlgCat (boolAlgColours l) (boolAlgColours r))
          (fun c hc => by
            rw [boolAlgListMem_cat, hc]; cases boolAlgListMem c (boolAlgColours l) <;> rfl)
          r ihr
      rw [hl, hr]
      rfl
  | joinOp l r ihl ihr =>
      show (boolAlgSupportedBy (boolAlgCat (boolAlgColours l) (boolAlgColours r)) l
        && boolAlgSupportedBy (boolAlgCat (boolAlgColours l) (boolAlgColours r)) r) = true
      have hl : boolAlgSupportedBy (boolAlgCat (boolAlgColours l) (boolAlgColours r)) l = true :=
        boolAlgSupported_weaken (boolAlgColours l)
          (boolAlgCat (boolAlgColours l) (boolAlgColours r))
          (fun c hc => by rw [boolAlgListMem_cat, hc]; rfl) l ihl
      have hr : boolAlgSupportedBy (boolAlgCat (boolAlgColours l) (boolAlgColours r)) r = true :=
        boolAlgSupported_weaken (boolAlgColours r)
          (boolAlgCat (boolAlgColours l) (boolAlgColours r))
          (fun c hc => by
            rw [boolAlgListMem_cat, hc]; cases boolAlgListMem c (boolAlgColours l) <;> rfl)
          r ihr
      rw [hl, hr]
      rfl
  | complOp u ihu => exact ihu

/-! ## The recursive Shannon decider and its correctness -/

/-- ★ **The recursive truth-table decider over a generator list.**  On the empty list, the trees are
closed (when supported) and we compare their single constant value.  On `g :: rest`, recurse on both
cofactors (`g := ⊤` and `g := ⊥`) — checking equality of truth tables on the sub-cube where `g` is
`true` and where `g` is `false`.  No mask enumeration: the generator list itself drives the recursion. -/
def boolAlgDecideOnGens : List Nat → BoolAlgTree → BoolAlgTree → Bool
  | [], s, t => boolAlgBoolEq (evalBoolAlgTree boolAlgFalseEnv s) (evalBoolAlgTree boolAlgFalseEnv t)
  | g :: rest, s, t =>
      boolAlgDecideOnGens rest (boolAlgSubstTop g s) (boolAlgSubstTop g t)
        && boolAlgDecideOnGens rest (boolAlgSubstBot g s) (boolAlgSubstBot g t)

/-- Soundness of the decision procedure: trees agreeing under every environment pass the decider. -/
theorem boolAlgDecideOnGens_of_evalAgree : ∀ (gens : List Nat) (s t : BoolAlgTree),
    (∀ env, evalBoolAlgTree env s = evalBoolAlgTree env t) →
      boolAlgDecideOnGens gens s t = true := by
  intro gens
  induction gens with
  | nil =>
      intro s t hAgree
      show boolAlgBoolEq (evalBoolAlgTree boolAlgFalseEnv s) (evalBoolAlgTree boolAlgFalseEnv t) = true
      rw [hAgree boolAlgFalseEnv]
      exact boolAlgBoolEq_refl _
  | cons g rest ih =>
      intro s t hAgree
      have hTop : ∀ env, evalBoolAlgTree env (boolAlgSubstTop g s)
          = evalBoolAlgTree env (boolAlgSubstTop g t) := by
        intro env
        rw [boolAlgEval_substTop env g s, boolAlgEval_substTop env g t]
        exact hAgree (boolAlgEnvSetTop g env)
      have hBot : ∀ env, evalBoolAlgTree env (boolAlgSubstBot g s)
          = evalBoolAlgTree env (boolAlgSubstBot g t) := by
        intro env
        rw [boolAlgEval_substBot env g s, boolAlgEval_substBot env g t]
        exact hAgree (boolAlgEnvSetBot g env)
      have h1 := ih (boolAlgSubstTop g s) (boolAlgSubstTop g t) hTop
      have h2 := ih (boolAlgSubstBot g s) (boolAlgSubstBot g t) hBot
      show (boolAlgDecideOnGens rest (boolAlgSubstTop g s) (boolAlgSubstTop g t)
        && boolAlgDecideOnGens rest (boolAlgSubstBot g s) (boolAlgSubstBot g t)) = true
      rw [h1, h2]
      rfl

/-- ★ **Completeness of the decision procedure**: if the decider passes on a list supporting both
trees, they are convertible.  Induction on the generator list peels one generator per step via the full
Shannon decomposition, recombining the two cofactor convertibilities from the IH; the empty base uses
`boolAlgClosedToConst`. -/
theorem boolAlgDecideOnGens_toConv : ∀ (gens : List Nat) (s t : BoolAlgTree),
    boolAlgSupportedBy gens s = true → boolAlgSupportedBy gens t = true →
      boolAlgDecideOnGens gens s t = true → BooleanAlgebraTreeConv s t := by
  intro gens
  induction gens with
  | nil =>
      intro s t hss hst hdec
      have heq : evalBoolAlgTree boolAlgFalseEnv s = evalBoolAlgTree boolAlgFalseEnv t :=
        boolAlgBoolEq_eq _ _ hdec
      have hs := boolAlgClosedToConst s hss
      have ht := boolAlgClosedToConst t hst
      exact (congrArg boolAlgConstOfBool heq ▸ hs).trans (BooleanAlgebraTreeConv.symm ht)
  | cons g rest ih =>
      intro s t hss hst hdec
      have hd1 : boolAlgDecideOnGens rest (boolAlgSubstTop g s) (boolAlgSubstTop g t) = true :=
        boolAlgAndTrueLeft _ _ hdec
      have hd2 : boolAlgDecideOnGens rest (boolAlgSubstBot g s) (boolAlgSubstBot g t) = true :=
        boolAlgAndTrueRight _ _ hdec
      have hsupTs := boolAlgSubstTop_supported g rest s hss
      have hsupTt := boolAlgSubstTop_supported g rest t hst
      have hsupBs := boolAlgSubstBot_supported g rest s hss
      have hsupBt := boolAlgSubstBot_supported g rest t hst
      have convTop := ih (boolAlgSubstTop g s) (boolAlgSubstTop g t) hsupTs hsupTt hd1
      have convBot := ih (boolAlgSubstBot g s) (boolAlgSubstBot g t) hsupBs hsupBt hd2
      have hs := boolAlgFullShannon g s
      have ht := boolAlgFullShannon g t
      have mid : BooleanAlgebraTreeConv
          (BoolAlgTree.joinOp
            (BoolAlgTree.meetOp (BoolAlgTree.gen g) (boolAlgSubstTop g s))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen g)) (boolAlgSubstBot g s)))
          (BoolAlgTree.joinOp
            (BoolAlgTree.meetOp (BoolAlgTree.gen g) (boolAlgSubstTop g t))
            (BoolAlgTree.meetOp (BoolAlgTree.complOp (BoolAlgTree.gen g)) (boolAlgSubstBot g t))) :=
        BooleanAlgebraTreeConv.joinCongr
          (BooleanAlgebraTreeConv.meetCongr (BooleanAlgebraTreeConv.refl (BoolAlgTree.gen g)) convTop)
          (BooleanAlgebraTreeConv.meetCongr
            (BooleanAlgebraTreeConv.refl (BoolAlgTree.complOp (BoolAlgTree.gen g))) convBot)
      exact hs.trans (mid.trans (BooleanAlgebraTreeConv.symm ht))

/-! ## The truth-table decision (the DECIDED outcome) -/

/-- ★ **The truth-table decision procedure** for `BooleanAlgebraTreeConv` — run the recursive Shannon
decider over the union of the two trees' collected colour lists.  Computes a `Bool`; correct by
`booleanAlgebraTreeConv_iff_truthTable`. -/
def decideBooleanAlgebraTreeConv (s t : BoolAlgTree) : Bool :=
  boolAlgDecideOnGens (boolAlgCat (boolAlgColours s) (boolAlgColours t)) s t

/-- ★★ **THE DECISION** — `BooleanAlgebraTreeConv s t` holds iff the truth-table decider returns `true`.
Forward is the Boolean-evaluation soundness (`booleanAlgebraTreeConv_eval_sound`) feeding the decider's
algorithm soundness; backward is the algorithm completeness (`boolAlgDecideOnGens_toConv`) after
establishing both trees are supported by the union colour list.  This makes convertibility in the free
bounded Boolean algebra on `ℕ` a genuine, complete DECISION — the completeness the file previously
walled at. -/
theorem booleanAlgebraTreeConv_iff_truthTable (s t : BoolAlgTree) :
    BooleanAlgebraTreeConv s t ↔ decideBooleanAlgebraTreeConv s t = true := by
  constructor
  · intro hconv
    exact boolAlgDecideOnGens_of_evalAgree (boolAlgCat (boolAlgColours s) (boolAlgColours t)) s t
      (fun env => booleanAlgebraTreeConv_eval_sound hconv env)
  · intro hdec
    have hss : boolAlgSupportedBy (boolAlgCat (boolAlgColours s) (boolAlgColours t)) s = true :=
      boolAlgSupported_weaken (boolAlgColours s)
        (boolAlgCat (boolAlgColours s) (boolAlgColours t))
        (fun c hc => by rw [boolAlgListMem_cat, hc]; rfl) s (boolAlgSelfSupported s)
    have hst : boolAlgSupportedBy (boolAlgCat (boolAlgColours s) (boolAlgColours t)) t = true :=
      boolAlgSupported_weaken (boolAlgColours t)
        (boolAlgCat (boolAlgColours s) (boolAlgColours t))
        (fun c hc => by
          rw [boolAlgListMem_cat, hc]; cases boolAlgListMem c (boolAlgColours s) <;> rfl)
        t (boolAlgSelfSupported t)
    exact boolAlgDecideOnGens_toConv (boolAlgCat (boolAlgColours s) (boolAlgColours t)) s t
      hss hst hdec

/-- ★ **Decidability of `BooleanAlgebraTreeConv`** — from the truth-table decision, with no `propext`
(the bridge is `Iff.mp`/`Iff.mpr`, never a Prop rewrite). -/
instance boolAlgDecidableConv (s t : BoolAlgTree) : Decidable (BooleanAlgebraTreeConv s t) :=
  if h : decideBooleanAlgebraTreeConv s t = true then
    isTrue ((booleanAlgebraTreeConv_iff_truthTable s t).mpr h)
  else
    isFalse (fun hconv => h ((booleanAlgebraTreeConv_iff_truthTable s t).mp hconv))

/-- Smoke: a generator is convertible to itself (decider returns `true`). -/
theorem decideBooleanAlgebraTreeConv_gen_refl :
    decideBooleanAlgebraTreeConv (BoolAlgTree.gen 0) (BoolAlgTree.gen 0) = true := rfl

/-- Smoke: distinct generators are NOT convertible (decider returns `false`). -/
theorem decideBooleanAlgebraTreeConv_gen_distinct :
    decideBooleanAlgebraTreeConv (BoolAlgTree.gen 0) (BoolAlgTree.gen 1) = false := rfl

/-- Smoke: commuted meets ARE convertible (decider returns `true`) — a nontrivial law decided by the
truth table. -/
theorem decideBooleanAlgebraTreeConv_meetComm_ex :
    decideBooleanAlgebraTreeConv
      (BoolAlgTree.meetOp (BoolAlgTree.gen 0) (BoolAlgTree.gen 1))
      (BoolAlgTree.meetOp (BoolAlgTree.gen 1) (BoolAlgTree.gen 0)) = true := rfl

/-- Smoke: the complement law `a ∧ ¬a ≈ ⊥` is decided `true`. -/
theorem decideBooleanAlgebraTreeConv_meetCompl_ex :
    decideBooleanAlgebraTreeConv
      (BoolAlgTree.meetOp (BoolAlgTree.gen 0) (BoolAlgTree.complOp (BoolAlgTree.gen 0)))
      BoolAlgTree.botOp = true := rfl

/-! ## The decision marker -/

/-- ★★ **The walking bounded Boolean algebra on an ARBITRARY alphabet — CONVERTIBILITY IS A GENUINE,
COMPLETE DECISION.**  `= true` records that the completeness the file previously walled at is now closed:
two trees are `BooleanAlgebraTreeConv`-related iff they have the same truth table, and that truth table
is checked by a terminating `Bool`-valued procedure (`decideBooleanAlgebraTreeConv`) with a full `↔`
correctness proof (`booleanAlgebraTreeConv_iff_truthTable`) and a `Decidable` instance.

The decision does NOT go through the minterm-list normal form (the previously-walled route, whose
combinatorial `boolAlgJoinTrueMinterms`-vs-truth-table assembly stayed open).  Instead it takes a cleaner
COMPLETE route via a recursive Shannon expansion over the generator list:

* the Conv-level De Morgan laws `booleanAlgebraDeMorganMeetConv` / `booleanAlgebraDeMorganJoinConv`
  (genuine `BooleanAlgebraTreeConv` derivations via `booleanAlgebraComplementUnique`, replacing the
  earlier eval-level-only De Morgan);
* the generator-substitution cofactor operators `boolAlgSubstTop` / `boolAlgSubstBot` and the crux
  paired double inductions `boolAlgGenRestrictTopPair` / `boolAlgGenRestrictBotPair` — meeting with
  `gen c` (resp. `¬gen c`) makes replacing `gen c` by `⊤` (resp. `⊥`) invisible, complemented subtree
  carried alongside (the exact fix for "complement is not monotone under a fixed meet"), whose
  binary-node complement subcases consume the Conv De Morgan laws;
* the full Shannon decomposition `boolAlgFullShannon` (`t ≈ (gen c ∧ t[c:=⊤]) ∨ (¬gen c ∧ t[c:=⊥])`);
* the recursive decider `boolAlgDecideOnGens` peeling one generator per step, with both correctness
  directions (`boolAlgDecideOnGens_of_evalAgree` = algorithm soundness from
  `booleanAlgebraTreeConv_eval_sound`; `boolAlgDecideOnGens_toConv` = completeness from the full Shannon
  peel plus the closed base `boolAlgClosedToConst`), tied off at the empty generator list where a
  supported tree is convertible to a constant.

The original SOUND floor and the minterm-DNF scaffolding (`boolAlgMintermOf` / `boolAlgAllMasks` /
`boolAlgMintermNF`, …) remain SHIPPED as an alternative canonical form; the decision above is
independent of them.  All declarations are zero-axiom: the finite `Bool` case-bashing is structural
(`Bool.rec` + `rfl`), the `Nat.beq` reflexivity/decision are purpose-built structural lemmas, the
list plumbing is cons-only, and no `List.append` (`++`), `Nat.le`/`Nat.ble` lemma, or `Int` appears
anywhere. -/
def fxWalkingBooleanAlgebra_hasTruthTableDecision : Bool := true

end FX1Poly.Polygraph
