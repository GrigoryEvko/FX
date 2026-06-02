import FX1Poly.OmegacE.Word

/-! # FX1Poly/OmegacE/Rewrite
    — the dimension-2 word-rewriting relation: word equality MODULO a rule system (Makkai/Forest, Path B)

The Makkai/Forest word-problem route (Path B of the three-way strong-normalization plan, polycell.md §2.3 /
§3.9) decides cell-equality in the free ω-category MODULO the FX rewrite rules.  `Word.lean` /
`WordFreeMonoid.lean` / `WordFreeMonoidUniversal.lean` built the dimension-1 layer: the free monoid on the
scaffold generators (`append`/`empty`, the universal property, `DecidableEq`, the length homomorphism) — so the
dim-1 word problem (free-monoid equality, no relations) is decidable by construction.

This file opens the dimension-2 layer: the rewriting relation that quotients words by a set of rules.  A rule
system is a SET (predicate) of rewrite rules; one-step rewriting fires a rule inside any left/right context
(the congruence is by construction); many-step rewriting is its reflexive-transitive closure.  This is exactly
"word equality modulo rewriting" — the structure whose decision (via convergence: termination + confluence,
Squier/Forest) is the Makkai word problem.

First genuine invariant: **length is preserved by rewriting under a length-preserving system** (both one-step
and many-step).  Length-preserving systems are the simplest convergent class (bounded search decides their
word problem), and the length homomorphism (`WordFreeMonoidUniversal.length_eq_foldOut`) is the tool — this is
the dim-2 reuse of the dim-1 free-monoid structure.  Plus the algebraic package: many-step rewriting is
reflexive (by ctor), transitive, and a two-sided congruence — i.e. a monoid-compatible preorder on words.

## Honest scope

This is the rewriting SUBSTRATE, not yet the word-problem DECISION.  It does NOT yet: connect the abstract
rule system to the concrete FX `Step` relation (the kernel↔ωcE bridge); prove termination or confluence of any
FX rule system; or decide word equality modulo a system.  Those are the subsequent Path-B atoms (convergent
presentation → Squier/Forest decidability).  The relation + closure + invariants here are the necessary
foundation they build on.

## Zero-axiom verification

The inductives carry no axioms; the theorems are structural inductions using `OmegacEWord.length_append` and
the ctor congruences.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- A dimension-2 rewrite rule between scaffold words at one dimension: rewrite the left-hand side to the
right-hand side. -/
structure OmegacERewriteRule (dimension : Nat) where
  /-- The pattern replaced by a rewrite. -/
  leftHandSide : OmegacEWord dimension
  /-- The replacement a rewrite installs. -/
  rightHandSide : OmegacEWord dimension

/-- **One-step rewriting under a rule system** (a set of rules), closed under left/right context — the
congruence with the free-monoid `append` is by construction (`underLeftContext`/`underRightContext`), so a
rule fires inside any surrounding word. -/
inductive OmegacEWord.RewritesOneStep {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) :
    OmegacEWord dimension → OmegacEWord dimension → Prop where
  | fire (rule : OmegacERewriteRule dimension) (isInSystem : system rule) :
      OmegacEWord.RewritesOneStep system rule.leftHandSide rule.rightHandSide
  | underLeftContext (prefixWord : OmegacEWord dimension)
      {sourceWord targetWord : OmegacEWord dimension}
      (inner : OmegacEWord.RewritesOneStep system sourceWord targetWord) :
      OmegacEWord.RewritesOneStep system
        (OmegacEWord.append prefixWord sourceWord)
        (OmegacEWord.append prefixWord targetWord)
  | underRightContext (suffixWord : OmegacEWord dimension)
      {sourceWord targetWord : OmegacEWord dimension}
      (inner : OmegacEWord.RewritesOneStep system sourceWord targetWord) :
      OmegacEWord.RewritesOneStep system
        (OmegacEWord.append sourceWord suffixWord)
        (OmegacEWord.append targetWord suffixWord)

/-- A rule system is length-preserving when every rule's two sides have equal length.  The simplest convergent
class: bounded search over equal-length words decides such a system's word problem. -/
def IsLengthPreservingSystem {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) : Prop :=
  ∀ rule : OmegacERewriteRule dimension, system rule →
    rule.leftHandSide.length = rule.rightHandSide.length

/-- **Length is a one-step rewrite invariant for length-preserving systems.**  By induction on the rewrite
derivation: the `fire` case is the system hypothesis; the context cases use `length_append` + the inner IH. -/
theorem OmegacEWord.RewritesOneStep.length_preserved {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (lengthPreserving : IsLengthPreservingSystem system)
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep system sourceWord targetWord) :
    sourceWord.length = targetWord.length := by
  induction step with
  | fire rule isInSystem => exact lengthPreserving rule isInSystem
  | underLeftContext prefixWord inner innerIH =>
      rw [OmegacEWord.length_append, OmegacEWord.length_append, innerIH]
  | underRightContext suffixWord inner innerIH =>
      rw [OmegacEWord.length_append, OmegacEWord.length_append, innerIH]

/-- **Many-step rewriting**: the reflexive-transitive closure of one-step rewriting — full word reduction
modulo the rule system. -/
inductive OmegacEWord.RewritesMany {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) :
    OmegacEWord dimension → OmegacEWord dimension → Prop where
  | refl (word : OmegacEWord dimension) : OmegacEWord.RewritesMany system word word
  | step {sourceWord middleWord targetWord : OmegacEWord dimension}
      (head : OmegacEWord.RewritesOneStep system sourceWord middleWord)
      (tail : OmegacEWord.RewritesMany system middleWord targetWord) :
      OmegacEWord.RewritesMany system sourceWord targetWord

/-- A single rewrite step is a many-step rewrite. -/
theorem OmegacEWord.RewritesMany.single {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep system sourceWord targetWord) :
    OmegacEWord.RewritesMany system sourceWord targetWord :=
  OmegacEWord.RewritesMany.step step (OmegacEWord.RewritesMany.refl targetWord)

/-- **Many-step rewriting is transitive** (compose two reduction sequences). -/
theorem OmegacEWord.RewritesMany.trans {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    {firstWord middleWord lastWord : OmegacEWord dimension}
    (firstToMiddle : OmegacEWord.RewritesMany system firstWord middleWord)
    (middleToLast : OmegacEWord.RewritesMany system middleWord lastWord) :
    OmegacEWord.RewritesMany system firstWord lastWord := by
  induction firstToMiddle with
  | refl _word => exact middleToLast
  | step head _tail tailIH => exact OmegacEWord.RewritesMany.step head (tailIH middleToLast)

/-- **Length is a many-step rewrite invariant for length-preserving systems.**  By induction on the reduction
sequence: `refl` is `rfl`; `step` chains the one-step invariant with the tail IH. -/
theorem OmegacEWord.RewritesMany.length_preserved {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (lengthPreserving : IsLengthPreservingSystem system)
    {sourceWord targetWord : OmegacEWord dimension}
    (many : OmegacEWord.RewritesMany system sourceWord targetWord) :
    sourceWord.length = targetWord.length := by
  induction many with
  | refl _word => rfl
  | step head _tail tailIH =>
      exact (head.length_preserved lengthPreserving).trans tailIH

/-- **Many-step rewriting is a congruence under a left context** — `append`-compatible on the left. -/
theorem OmegacEWord.RewritesMany.underLeftContext {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (prefixWord : OmegacEWord dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (many : OmegacEWord.RewritesMany system sourceWord targetWord) :
    OmegacEWord.RewritesMany system
      (OmegacEWord.append prefixWord sourceWord)
      (OmegacEWord.append prefixWord targetWord) := by
  induction many with
  | refl word => exact OmegacEWord.RewritesMany.refl (OmegacEWord.append prefixWord word)
  | step head _tail tailIH =>
      exact OmegacEWord.RewritesMany.step (head.underLeftContext prefixWord) tailIH

/-- **Many-step rewriting is a congruence under a right context** — `append`-compatible on the right. -/
theorem OmegacEWord.RewritesMany.underRightContext {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (suffixWord : OmegacEWord dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (many : OmegacEWord.RewritesMany system sourceWord targetWord) :
    OmegacEWord.RewritesMany system
      (OmegacEWord.append sourceWord suffixWord)
      (OmegacEWord.append targetWord suffixWord) := by
  induction many with
  | refl word => exact OmegacEWord.RewritesMany.refl (OmegacEWord.append word suffixWord)
  | step head _tail tailIH =>
      exact OmegacEWord.RewritesMany.step (head.underRightContext suffixWord) tailIH

/-! ## Convertibility modulo a system — the presented monoid

`RewritesMany` is the directed reduction; its reflexive-symmetric-transitive closure is `ConvertibleModulo`,
equality in the monoid PRESENTED by the rule system (generators = scaffold cells, relations = the rules).  This
is exactly what the Makkai word problem decides.  Convertibility is an equivalence and a two-sided congruence,
so the quotient is a monoid; and length is a convertibility invariant for length-preserving systems — the
SEPARATING invariant (different lengths ⟹ not convertible, a checkable necessary condition). -/

/-- **Word convertibility modulo a rule system**: the reflexive-symmetric-transitive closure of one-step
rewriting — equality in the presented monoid (the relation the word problem decides). -/
inductive OmegacEWord.ConvertibleModulo {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) :
    OmegacEWord dimension → OmegacEWord dimension → Prop where
  | ofStep {sourceWord targetWord : OmegacEWord dimension}
      (step : OmegacEWord.RewritesOneStep system sourceWord targetWord) :
      OmegacEWord.ConvertibleModulo system sourceWord targetWord
  | refl (word : OmegacEWord dimension) : OmegacEWord.ConvertibleModulo system word word
  | symm {sourceWord targetWord : OmegacEWord dimension}
      (converts : OmegacEWord.ConvertibleModulo system sourceWord targetWord) :
      OmegacEWord.ConvertibleModulo system targetWord sourceWord
  | trans {firstWord middleWord lastWord : OmegacEWord dimension}
      (firstToMiddle : OmegacEWord.ConvertibleModulo system firstWord middleWord)
      (middleToLast : OmegacEWord.ConvertibleModulo system middleWord lastWord) :
      OmegacEWord.ConvertibleModulo system firstWord lastWord

/-- A many-step reduction is a convertibility (the forward embedding `RewritesMany ⊆ ConvertibleModulo`). -/
theorem OmegacEWord.ConvertibleModulo.ofRewritesMany {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    {sourceWord targetWord : OmegacEWord dimension}
    (many : OmegacEWord.RewritesMany system sourceWord targetWord) :
    OmegacEWord.ConvertibleModulo system sourceWord targetWord := by
  induction many with
  | refl word => exact OmegacEWord.ConvertibleModulo.refl word
  | step head _tail tailIH =>
      exact OmegacEWord.ConvertibleModulo.trans (OmegacEWord.ConvertibleModulo.ofStep head) tailIH

/-- **Convertibility modulo a system is an equivalence relation** — so the quotient by it is well-defined
(the presented monoid's carrier). -/
theorem OmegacEWord.ConvertibleModulo.equivalence {dimension : Nat}
    (system : OmegacERewriteRule dimension → Prop) :
    Equivalence (OmegacEWord.ConvertibleModulo system) :=
  { refl := OmegacEWord.ConvertibleModulo.refl
    symm := OmegacEWord.ConvertibleModulo.symm
    trans := OmegacEWord.ConvertibleModulo.trans }

/-- Convertibility is a congruence under a left context — `append`-compatible, so the quotient inherits a
monoid multiplication. -/
theorem OmegacEWord.ConvertibleModulo.underLeftContext {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (prefixWord : OmegacEWord dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (converts : OmegacEWord.ConvertibleModulo system sourceWord targetWord) :
    OmegacEWord.ConvertibleModulo system
      (OmegacEWord.append prefixWord sourceWord)
      (OmegacEWord.append prefixWord targetWord) := by
  induction converts with
  | ofStep step => exact OmegacEWord.ConvertibleModulo.ofStep (step.underLeftContext prefixWord)
  | refl word => exact OmegacEWord.ConvertibleModulo.refl (OmegacEWord.append prefixWord word)
  | symm _converts convertsIH => exact OmegacEWord.ConvertibleModulo.symm convertsIH
  | trans _firstToMiddle _middleToLast firstIH middleIH =>
      exact OmegacEWord.ConvertibleModulo.trans firstIH middleIH

/-- Convertibility is a congruence under a right context — `append`-compatible on the right. -/
theorem OmegacEWord.ConvertibleModulo.underRightContext {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (suffixWord : OmegacEWord dimension)
    {sourceWord targetWord : OmegacEWord dimension}
    (converts : OmegacEWord.ConvertibleModulo system sourceWord targetWord) :
    OmegacEWord.ConvertibleModulo system
      (OmegacEWord.append sourceWord suffixWord)
      (OmegacEWord.append targetWord suffixWord) := by
  induction converts with
  | ofStep step => exact OmegacEWord.ConvertibleModulo.ofStep (step.underRightContext suffixWord)
  | refl word => exact OmegacEWord.ConvertibleModulo.refl (OmegacEWord.append word suffixWord)
  | symm _converts convertsIH => exact OmegacEWord.ConvertibleModulo.symm convertsIH
  | trans _firstToMiddle _middleToLast firstIH middleIH =>
      exact OmegacEWord.ConvertibleModulo.trans firstIH middleIH

/-- **Length is a convertibility invariant for length-preserving systems** — the SEPARATING invariant: words
of different lengths are NOT convertible, a checkable necessary condition for the word problem. -/
theorem OmegacEWord.ConvertibleModulo.length_preserved {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (lengthPreserving : IsLengthPreservingSystem system)
    {sourceWord targetWord : OmegacEWord dimension}
    (converts : OmegacEWord.ConvertibleModulo system sourceWord targetWord) :
    sourceWord.length = targetWord.length := by
  induction converts with
  | ofStep step => exact step.length_preserved lengthPreserving
  | refl _word => rfl
  | symm _converts convertsIH => exact convertsIH.symm
  | trans _firstToMiddle _middleToLast firstIH middleIH => exact firstIH.trans middleIH

end FX1Poly.OmegacE
